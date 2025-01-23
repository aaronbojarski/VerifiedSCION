// Copyright 2022 ETH Zurich
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// +gobra

package spao

import (
	"crypto/aes"
	"encoding/binary"
	"fmt"
	"hash"

	"github.com/dchest/cmac"

	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/slayers"
	"github.com/scionproto/scion/pkg/slayers/path"
	"github.com/scionproto/scion/pkg/slayers/path/empty"
	"github.com/scionproto/scion/pkg/slayers/path/epic"
	"github.com/scionproto/scion/pkg/slayers/path/onehop"
	"github.com/scionproto/scion/pkg/slayers/path/scion"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	// @ "github.com/scionproto/scion/pkg/addr"
)

const (
	// FixAuthDataInputLen is the unvariable fields length for the
	// authenticated data. It consists of the Authenticator Option Metadata
	// length and the SCION Common Header without the second row.
	fixAuthDataInputLen = slayers.PacketAuthOptionMetadataLen +
		slayers.CmnHdrLen - slayers.LineLen
	// MACBufferSize sets an upperBound to the authenticated data
	// length (excluding the payload). This is:
	// 1. Authenticator Option Meta
	// 2. SCION Common Header
	// 3. SCION Address Header
	// 4. Path
	// (see https://docs.scion.org/en/latest/protocols/authenticator-option.html#authenticated-data)
	// We round this up to 12B (authenticator option meta) + 1020B (max SCION header length)
	// To adapt to any possible path types.
	MACBufferSize = 1032
)

type MACInput struct {
	Key        []byte
	Header     slayers.PacketAuthOption
	ScionLayer *slayers.SCION
	PldType    slayers.L4ProtocolType
	Pld        []byte
}

// ComputeAuthCMAC computes the authenticator tag for the AES-CMAC algorithm.
// The key should correspond to the SPI defined in opt.SPI.
// The SCION layer, payload type and payload define the input to the MAC, as defined in
// https://docs.scion.org/en/latest/protocols/authenticator-option.html#authenticated-data.
//
// The aux buffer is used as a temporary buffer for the MAC computation.
// It must be at least MACBufferSize long.
// The resulting MAC is written to outBuffer (appending, if necessary),
// and returned as a slice of length 16.

// @ requires  len(auxBuffer) >= MACBufferSize
// @ requires  len(outBuffer) >= aes.BlockSize
// @ requires  acc(input.ScionLayer.Mem(ubuf), R8)
// @ requires  input.Valid(ubuf)
// @ preserves acc(sl.Bytes(input.Key, 0, len(input.Key)), R50)
// @ preserves acc(input.Header.EndToEndOption, R48)
// @ preserves len(input.Header.OptData) >= 12
// @ preserves acc(sl.Bytes(input.Header.OptData, 0, len(input.Header.OptData)), R49)
// @ preserves acc(sl.Bytes(input.Pld, 0, len(input.Pld)), R6)
// @ preserves sl.Bytes(auxBuffer, 0, len(auxBuffer))
// @ preserves sl.Bytes(outBuffer, 0, len(outBuffer))
// @ preserves sl.Bytes(ubuf, 0, len(ubuf))
// @ ensures   acc(input.ScionLayer.Mem(ubuf), R8)
// @ ensures   retErr != nil ==> retErr.ErrorMem()
// @ decreases
func ComputeAuthCMAC(
	input MACInput,
	auxBuffer []byte,
	outBuffer []byte,
	/*@ ghost ubuf []byte, @*/
) (b []byte, retErr error) {

	cmac, err := initCMAC(input.Key)
	if err != nil {
		return nil, err
	}
	inputLen, err := serializeAuthenticatedData(
		auxBuffer,
		input.ScionLayer,
		input.Header,
		input.PldType,
		input.Pld,
		/*@ ubuf, @*/
	)
	if err != nil {
		return nil, err
	}
	// @ sl.SplitRange_Bytes(auxBuffer, 0, inputLen, R1)
	// @ unfold acc(sl.Bytes(auxBuffer[:inputLen], 0, inputLen), R1)
	cmac.Write(auxBuffer[:inputLen])
	// @ fold acc(sl.Bytes(auxBuffer[:inputLen], 0, inputLen), R1)
	// @ sl.CombineRange_Bytes(auxBuffer, 0, inputLen, R1)

	// @ unfold acc(sl.Bytes(input.Pld, 0, len(input.Pld)), R7)
	cmac.Write(input.Pld)
	// @ fold acc(sl.Bytes(input.Pld, 0, len(input.Pld)), R7)
	return cmac.Sum(outBuffer[:0]), nil
}

// @ preserves acc(sl.Bytes(key, 0, len(key)), R50)
// @ ensures   retErr == nil ==> m.Mem() && typeOf(m) == type[*cmac.cmac]
// @ ensures   retErr != nil ==> retErr.ErrorMem()
// @ decreases
func initCMAC(key []byte) (m hash.Hash, retErr error) {
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, serrors.Wrap("unable to initialize AES cipher", err)
	}
	mac, err := cmac.New(block)
	if err != nil {
		return nil, serrors.Wrap("unable to initialize Mac", err)
	}
	return mac, nil
}

// @ requires  len(buf) >= MACBufferSize
// @ preserves sl.Bytes(buf, 0, len(buf))
// @ preserves sl.Bytes(ubuf, 0, len(ubuf))
// @ preserves s != nil
// @ preserves acc(s.Mem(ubuf), R8)
// @ preserves s.ValidPathMetaData(ubuf)
// @ preserves acc(opt.EndToEndOption, R48)
// @ preserves len(opt.OptData) >= 12
// @ preserves acc(sl.Bytes(opt.OptData, 0, len(opt.OptData)), R49)
// @ preserves acc(sl.Bytes(pld, 0, len(pld)), R50)
// @ ensures   0 <= n && n <= MACBufferSize
// @ ensures   retErr != nil ==> retErr.ErrorMem()
// @ decreases
func serializeAuthenticatedData(
	buf []byte,
	s *slayers.SCION,
	opt slayers.PacketAuthOption,
	pldType slayers.L4ProtocolType,
	pld []byte,
	/*@ ghost ubuf []byte, @*/
) (n int, retErr error) {
	// @ preserves len(buf) >= MACBufferSize && sl.Bytes(buf, 0, len(buf))
	// @ decreases
	// @ outline (
	// @ unfold sl.Bytes(buf, 0, len(buf))
	_ = buf[MACBufferSize-1]
	// @ fold sl.Bytes(buf, 0, len(buf))
	// @ )
	// @ unfold acc(s.Mem(ubuf), R50)
	hdrLen := slayers.CmnHdrLen + s.AddrHdrLen( /*@ ubuf, false @*/ ) + s.Path.Len( /*@ s.UBPath(ubuf) @*/ )
	// @ fold acc(s.Mem(ubuf), R50)
	if hdrLen > slayers.MaxHdrLen {
		return 0, serrors.New("SCION header length exceeds maximum",
			"max", slayers.MaxHdrLen, "actual", hdrLen)
	}
	if hdrLen%slayers.LineLen != 0 {
		return 0, serrors.New("SCION header length is not an integer multiple of line length",
			"actual", hdrLen)
	}

	// @ preserves len(buf) >= MACBufferSize && sl.Bytes(buf, 0, len(buf))
	// @ preserves acc(s.Mem(ubuf), R50)
	// @ preserves acc(opt.EndToEndOption, R49)
	// @ preserves len(opt.OptData) >= 12
	// @ preserves acc(sl.Bytes(opt.OptData, 0, len(opt.OptData)), R50)
	// @ ensures   fixAuthDataInputLen <= offset && offset <= fixAuthDataInputLen + 16
	// @ decreases
	// @ outline (
	// @ unfold sl.Bytes(buf, 0, len(buf))
	buf[0] = byte(hdrLen / slayers.LineLen)
	buf[1] = byte(pldType)
	// @ assert &buf[2:][0] == &buf[2 + 0] && &buf[2:][1] == &buf[2 + 1]
	binary.BigEndian.PutUint16(buf[2:], uint16(len(pld)))
	buf[4] = byte(opt.Algorithm())
	buf[5] = byte(0)
	// @ assert &buf[6:12][0] == &buf[6 + 0] && &buf[6:12][1] == &buf[6 + 1]
	// @ assert &buf[6:12][2] == &buf[6 + 2] && &buf[6:12][3] == &buf[6 + 3]
	// @ assert &buf[6:12][4] == &buf[6 + 4] && &buf[6:12][5] == &buf[6 + 5]
	bigEndianPutUint48(buf[6:12], opt.TimestampSN())
	// @ unfold acc(s.Mem(ubuf), R50)
	firstHdrLine := uint32(s.Version&0xF)<<28 | uint32(s.TrafficClass&0x3f)<<20 | s.FlowID&0xFFFFF
	// @ assert &buf[12:][0] == &buf[12 + 0] && &buf[12:][1] == &buf[12 + 1]
	// @ assert &buf[12:][2] == &buf[12 + 2] && &buf[12:][3] == &buf[12 + 3]
	binary.BigEndian.PutUint32(buf[12:], firstHdrLine)
	buf[16] = byte(s.PathType)
	buf[17] = byte(s.DstAddrType&0xF)<<4 | byte(s.SrcAddrType&0xF)
	// @ assert &buf[18:][0] == &buf[18 + 0] && &buf[18:][1] == &buf[18 + 1]
	binary.BigEndian.PutUint16(buf[18:], 0)

	offset := fixAuthDataInputLen

	if !opt.SPI().IsDRKey() {
		// @ unfold acc(s.HeaderMem(ubuf[slayers.CmnHdrLen:]), R50)
		// @ sl.AssertSliceOverlap(buf, offset, len(buf))
		binary.BigEndian.PutUint64(buf[offset:], uint64(s.DstIA))
		// @ sl.AssertSliceOverlap(buf, offset+8, len(buf))
		binary.BigEndian.PutUint64(buf[offset+8:], uint64(s.SrcIA))
		// @ fold acc(s.HeaderMem(ubuf[slayers.CmnHdrLen:]), R50)
		offset += 16
	}
	// @ fold acc(s.Mem(ubuf), R50)
	// @ fold sl.Bytes(buf, 0, len(buf))
	// @ )

	// @ unfold acc(s.Mem(ubuf), R9)
	// @ defer fold acc(s.Mem(ubuf), R9)
	// @ unfold acc(s.HeaderMem(ubuf[slayers.CmnHdrLen:]), R10)
	if !opt.SPI().IsDRKey() ||
		(opt.SPI().Type() == slayers.PacketAuthASHost &&
			opt.SPI().Direction() == slayers.PacketAuthReceiverSide) {
		// @ dstAddrBytes := s.DstAddrType.Length()
		// @ ubufOffset := slayers.CmnHdrLen + 2 * addr.IABytes
		// @ copyOffset := offset
		// @ sl.SplitRange_Bytes(buf, copyOffset, len(buf), writePerm)
		// @ sl.SplitRange_Bytes(ubuf, ubufOffset, ubufOffset+dstAddrBytes, R10)
		// @ unfold sl.Bytes(buf[copyOffset:], 0, len(buf[copyOffset:]))
		// @ unfold acc(sl.Bytes(ubuf[ubufOffset:ubufOffset+dstAddrBytes], 0, len(ubuf[ubufOffset:ubufOffset+dstAddrBytes])), R10)
		offset += copy(buf[offset:], s.RawDstAddr /*@ , R10 @*/)
		// @ fold sl.Bytes(buf[copyOffset:], 0, len(buf[copyOffset:]))
		// @ fold acc(sl.Bytes(ubuf[ubufOffset:ubufOffset+dstAddrBytes], 0, len(ubuf[ubufOffset:ubufOffset+dstAddrBytes])), R10)
		// @ sl.CombineRange_Bytes(buf, copyOffset, len(buf), writePerm)
		// @ sl.CombineRange_Bytes(ubuf, ubufOffset, ubufOffset+dstAddrBytes, R10)
	}
	if !opt.SPI().IsDRKey() ||
		(opt.SPI().Type() == slayers.PacketAuthASHost &&
			opt.SPI().Direction() == slayers.PacketAuthSenderSide) {
		// @ srcAddrBytes := s.SrcAddrType.Length()
		// @ ubufOffset := slayers.CmnHdrLen + 2 * addr.IABytes + s.DstAddrType.Length()
		// @ copyOffset := offset
		// @ sl.SplitRange_Bytes(buf, copyOffset, len(buf), writePerm)
		// @ sl.SplitRange_Bytes(ubuf, ubufOffset, ubufOffset+srcAddrBytes, R10)
		// @ unfold sl.Bytes(buf[copyOffset:], 0, len(buf[copyOffset:]))
		// @ unfold acc(sl.Bytes(ubuf[ubufOffset:ubufOffset+srcAddrBytes], 0, len(ubuf[ubufOffset:ubufOffset+srcAddrBytes])), R10)
		offset += copy(buf[offset:], s.RawSrcAddr /*@ , R10 @*/)
		// @ fold sl.Bytes(buf[copyOffset:], 0, len(buf[copyOffset:]))
		// @ fold acc(sl.Bytes(ubuf[ubufOffset:ubufOffset+srcAddrBytes], 0, len(ubuf[ubufOffset:ubufOffset+srcAddrBytes])), R10)
		// @ sl.CombineRange_Bytes(buf, copyOffset, len(buf), writePerm)
		// @ sl.CombineRange_Bytes(ubuf, ubufOffset, ubufOffset+srcAddrBytes, R10)
	}
	// @ fold acc(s.HeaderMem(ubuf[slayers.CmnHdrLen:]), R10)

	// @ sl.SplitRange_Bytes(buf, offset, len(buf), writePerm)
	// @ sl.SplitRange_Bytes(ubuf, int(slayers.CmnHdrLen+s.AddrHdrLenSpecInternal()), int(s.HdrLen*slayers.LineLen), writePerm)
	err := zeroOutMutablePath(s.Path, buf[offset:] /*@, s.UBPath(ubuf) @*/)
	// @ sl.CombineRange_Bytes(buf, offset, len(buf), writePerm)
	// @ sl.CombineRange_Bytes(ubuf, int(slayers.CmnHdrLen+s.AddrHdrLenSpecInternal()), int(s.HdrLen*slayers.LineLen), writePerm)
	if err != nil {
		return 0, err
	}
	offset += s.Path.Len( /*@ s.UBPath(ubuf) @*/ )
	return offset, nil
}

// @ requires  orig != nil
// @ requires  len(buf) >=  28 + 12 * scion.MaxHops + epic.MetadataLen
// @ requires  acc(orig.Mem(ubuf), R9)
// @ requires  (typeOf(orig) == type[*scion.Raw] ==>
// @				orig.(*scion.Raw).GetBase(ubuf).WeaklyValid()) &&
// @		   (typeOf(orig) == type[*scion.Decoded] ==>
// @				orig.(*scion.Decoded).GetBase(ubuf).WeaklyValid()) &&
// @		   (typeOf(orig) == type[*epic.Path] ==>
// @				orig.(*epic.Path).GetBase(ubuf).WeaklyValid())
// @ preserves sl.Bytes(buf, 0, len(buf))
// @ preserves sl.Bytes(ubuf, 0, len(ubuf))
// @ ensures   acc(orig.Mem(ubuf), R9)
// @ ensures   retErr != nil ==> retErr.ErrorMem()
// @ decreases
func zeroOutMutablePath(orig path.Path, buf []byte /*@, ghost ubuf []byte @*/) (retErr error) {
	err := orig.SerializeTo(buf /*@, ubuf @*/)
	if err != nil {
		return serrors.Wrap("serializing path for resetting fields", err)
	}
	switch p := orig.(type) {
	case empty.Path:
		return nil
	case *scion.Raw:
		// @ unfold acc(p.Mem(ubuf), R50)
		// @ unfold acc(p.Base.Mem(), R50)
		zeroOutWithBase(p.Base, buf)
		// @ fold acc(p.Base.Mem(), R50)
		// @ fold acc(p.Mem(ubuf), R50)
		return nil
	case *scion.Decoded:
		// @ unfold acc(p.Mem(ubuf), R50)
		// @ unfold acc(p.Base.Mem(), R50)
		zeroOutWithBase(p.Base, buf)
		// @ fold acc(p.Base.Mem(), R50)
		// @ fold acc(p.Mem(ubuf), R50)
		return nil
	case *epic.Path:
		// @ unfold acc(p.Mem(ubuf), R50)
		// @ unfold acc(p.ScionPath.Mem(ubuf[epic.MetadataLen:]), R50)
		// @ unfold acc(p.ScionPath.Base.Mem(), R50)
		// @ sl.SplitRange_Bytes(buf, epic.MetadataLen, len(buf), writePerm)
		zeroOutWithBase(p.ScionPath.Base, buf[epic.MetadataLen:])
		// @ sl.CombineRange_Bytes(buf, epic.MetadataLen, len(buf), writePerm)
		// @ fold acc(p.ScionPath.Base.Mem(), R50)
		// @ fold acc(p.ScionPath.Mem(ubuf[epic.MetadataLen:]), R50)
		// @ fold acc(p.Mem(ubuf), R50)
		return nil
	case *onehop.Path:
		// Zero out IF.SegID
		// @ unfold sl.Bytes(buf, 0, len(buf))
		// @ sl.AssertSliceOverlap(buf, 2, len(buf))
		binary.BigEndian.PutUint16(buf[2:], 0)
		// Zero out HF.Flags&&Alerts
		buf[8] = 0
		// Zero out second HF
		// @ sl.AssertSliceOverlap(buf, 20, len(buf))
		copy(buf[20:], []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0} /*@ , R20 @*/)
		// @ fold sl.Bytes(buf, 0, len(buf))
		return nil
	default:
		return serrors.New(fmt.Sprintf("unknown path type %T", orig))
	}
}

// @ requires  len(buf) >= 28 + 12 * scion.MaxHops
// @ requires  base.WeaklyValid()
// @ preserves sl.Bytes(buf, 0, len(buf))
// @ decreases
func zeroOutWithBase(base scion.Base, buf []byte) {
	// Zero out CurrInf && CurrHF
	offset := 0
	// @ unfold sl.Bytes(buf, 0, len(buf))
	buf[offset] = 0
	// @ fold sl.Bytes(buf, 0, len(buf))
	offset += 4

	// @ invariant 0 <= i && i <= base.NumINF
	// @ invariant offset == 4 + 8*i
	// @ invariant 4 <= offset && offset <= 28
	// @ invariant sl.Bytes(buf, 0, len(buf))
	// @ decreases base.NumINF - i
	for i := 0; i < base.NumINF; i++ {
		// Zero out IF.SegID
		// @ unfold sl.Bytes(buf, 0, len(buf))
		// @ sl.AssertSliceOverlap(buf, offset+2, len(buf))
		binary.BigEndian.PutUint16(buf[offset+2:], 0)
		// @ fold sl.Bytes(buf, 0, len(buf))
		offset += 8
	}
	// @ oldOffset := offset
	// @ invariant base.WeaklyValid()
	// @ invariant 0 <= i && i <= base.NumINF
	// @ invariant i == 0 ==> offset == oldOffset
	// @ invariant i == 1 ==> offset == oldOffset + 12 * int(base.PathMeta.SegLen[0])
	// @ invariant i == 2 ==> offset == oldOffset + 12 * (int(base.PathMeta.SegLen[0]) + int(base.PathMeta.SegLen[1]))
	// @ invariant i == 3 ==> offset == oldOffset + 12 * (int(base.PathMeta.SegLen[0]) + int(base.PathMeta.SegLen[1]) + int(base.PathMeta.SegLen[2]))
	// @ invariant sl.Bytes(buf, 0, len(buf))
	// @ decreases base.NumINF - i
	for i := 0; i < base.NumINF; i++ {
		// @ oldOffsetInner := offset
		// @ invariant base.WeaklyValid()
		// @ invariant i < base.NumINF
		// @ invariant 0 <= j && j <= int(base.PathMeta.SegLen[i])
		// @ invariant offset == oldOffsetInner + 12 * j
		// @ invariant 4 <= offset && offset <= oldOffset + 12 * scion.MaxHops
		// @ invariant sl.Bytes(buf, 0, len(buf))
		// @ decreases int(base.PathMeta.SegLen[i]) - j
		for j := 0; j < int(base.PathMeta.SegLen[i]); j++ {
			// Zero out HF.Flags&&Alerts
			// @ unfold sl.Bytes(buf, 0, len(buf))
			buf[offset] = 0
			// @ fold sl.Bytes(buf, 0, len(buf))
			offset += 12
		}
	}
}

// @ requires  len(b) >= 6
// @ preserves acc(&b[0]) && acc(&b[1]) && acc(&b[2]) && acc(&b[3]) && acc(&b[4]) && acc(&b[5])
// @ decreases
func bigEndianPutUint48(b []byte, v uint64) {
	b[0] = byte(v >> 40)
	b[1] = byte(v >> 32)
	// @ assert &b[2:6][0] == &b[2 + 0] && &b[2:6][1] == &b[2 + 1]
	// @ assert &b[2:6][2] == &b[2 + 2] && &b[2:6][3] == &b[2 + 3]
	binary.BigEndian.PutUint32(b[2:6], uint32(v))
}
