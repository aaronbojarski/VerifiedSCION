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

// @ requires  acc(sl.Bytes(input.Key, 0, len(input.Key)), R50)
// @ preserves sl.Bytes(auxBuffer, 0, len(auxBuffer))
// @ preserves sl.Bytes(outBuffer, 0, len(outBuffer))
// @ ensures   sl.Bytes(b, 0, len(b))
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
	cmac.Write(auxBuffer[:inputLen])
	cmac.Write(input.Pld)
	return cmac.Sum(outBuffer[:0]), nil
}

// @ requires  acc(sl.Bytes(key, 0, len(key)), R50)
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

// @ requires  s != nil
// @ requires  acc(pld, _)
// @ requires  len(buf) >= MACBufferSize
// @ preserves sl.Bytes(buf, 0, len(buf))
// @ preserves acc(s, R49)
// @ preserves acc(s.Mem(ubuf), R49)
// @ preserves acc(s.Path.Mem(ubuf), R49)
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

	// @ unfold sl.Bytes(buf, 0, len(buf))
	_ = buf[MACBufferSize-1]
	// @ unfold acc(s.Mem(ubuf), R50)
	// @ defer fold acc(s.Mem(ubuf), R50)
	hdrLen := slayers.CmnHdrLen + s.AddrHdrLen( /*@ ubuf, false @*/ ) + s.Path.Len( /*@ ubuf @*/ )
	if hdrLen > slayers.MaxHdrLen {
		// @ fold sl.Bytes(buf, 0, len(buf))
		return 0, serrors.New("SCION header length exceeds maximum",
			"max", slayers.MaxHdrLen, "actual", hdrLen)
	}
	if hdrLen%slayers.LineLen != 0 {
		// @ fold sl.Bytes(buf, 0, len(buf))
		return 0, serrors.New("SCION header length is not an integer multiple of line length",
			"actual", hdrLen)
	}

	buf[0] = byte(hdrLen / slayers.LineLen)
	buf[1] = byte(pldType)
	// @ assert forall j int :: { &buf[2:][j] } 0 <= 2 ==> &buf[2:][j] == &buf[2 + j]
	binary.BigEndian.PutUint16(buf[2:], uint16(len(pld)))
	buf[4] = byte(opt.Algorithm())
	buf[5] = byte(0)
	//@ assert forall j int :: { &buf[6:12][j] } 0 <= 6 ==> &buf[6:12][j] == &buf[6 + j]
	bigEndianPutUint48(buf[6:12], opt.TimestampSN())
	firstHdrLine := uint32(s.Version&0xF)<<28 | uint32(s.TrafficClass&0x3f)<<20 | s.FlowID&0xFFFFF
	// @ assert forall j int :: { &buf[12:][j] } 0 <= 4 ==> &buf[12:][j] == &buf[12 + j]
	binary.BigEndian.PutUint32(buf[12:], firstHdrLine)
	buf[16] = byte(s.PathType)
	buf[17] = byte(s.DstAddrType&0xF)<<4 | byte(s.SrcAddrType&0xF)
	// @ assert forall j int :: { &buf[18:][j] } 0 <= 2 ==> &buf[18:][j] == &buf[18 + j]
	binary.BigEndian.PutUint16(buf[18:], 0)
	offset := fixAuthDataInputLen

	if !opt.SPI().IsDRKey() {
		// @ assert forall j int :: { &buf[offset:][j] } 0 <= 8 ==> &buf[offset:][j] == &buf[offset + j]
		binary.BigEndian.PutUint64(buf[offset:], uint64(s.DstIA))
		// @ assert forall j int :: { &buf[offset+8:][j] } 0 <= 8 ==> &buf[offset+8:][j] == &buf[offset+8 + j]
		binary.BigEndian.PutUint64(buf[offset+8:], uint64(s.SrcIA))
		offset += 16
	}
	// @ fold sl.Bytes(buf, 0, len(buf))
	if !opt.SPI().IsDRKey() ||
		(opt.SPI().Type() == slayers.PacketAuthASHost &&
			opt.SPI().Direction() == slayers.PacketAuthReceiverSide) {
		// @ sl.SplitRange_Bytes(buf, offset, len(buf), writePerm)
		offset += copy(buf[offset:], s.RawDstAddr /*@ , R20 @*/)
		// @ sl.CombineRange_Bytes(buf, offset, len(buf), writePerm)
	}
	if !opt.SPI().IsDRKey() ||
		(opt.SPI().Type() == slayers.PacketAuthASHost &&
			opt.SPI().Direction() == slayers.PacketAuthSenderSide) {
		// @ sl.SplitRange_Bytes(buf, offset, len(buf), writePerm)
		offset += copy(buf[offset:], s.RawSrcAddr /*@ , R20 @*/)
		// @ sl.CombineRange_Bytes(buf, offset, len(buf), writePerm)
	}
	// @ sl.SplitRange_Bytes(buf, offset, len(buf), writePerm)
	err := zeroOutMutablePath(s.Path, buf[offset:] /*@, ubuf @*/)
	// @ sl.CombineRange_Bytes(buf, offset, len(buf), writePerm)
	if err != nil {
		return 0, err
	}
	offset += s.Path.Len( /*@ ubuf @*/ )
	return offset, nil
}

// @ requires  orig != nil
// @ requires  len(buf) >= MACBufferSize
// @ preserves acc(orig.Mem(ubuf), R1)
// @ preserves sl.Bytes(ubuf, 0, len(ubuf))
// @ preserves sl.Bytes(buf, 0, len(buf))
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
		// @ unfold acc(p.Mem(ubuf), R1)
		// @ unfold acc(p.Base.Mem(), R1)
		zeroOutWithBase(p.Base, buf)
		// @ fold acc(p.Base.Mem(), R1)
		// @ fold acc(p.Mem(ubuf), R1)
		return nil
	case *scion.Decoded:
		// @ unfold acc(p.Mem(ubuf), R1)
		// @ unfold acc(p.Base.Mem(), R1)
		zeroOutWithBase(p.Base, buf)
		// @ fold acc(p.Base.Mem(), R1)
		// @ fold acc(p.Mem(ubuf), R1)
		return nil
	case *epic.Path:
		// @ unfold acc(p.Mem(ubuf), R1)
		// @ unfold acc(p.ScionPath.Mem(ubuf[epic.MetadataLen:]), R1)
		// @ unfold acc(p.ScionPath.Base.Mem(), R1)
		// @ sl.SplitRange_Bytes(buf, epic.MetadataLen, len(buf), writePerm)
		zeroOutWithBase(p.ScionPath.Base, buf[epic.MetadataLen:])
		// @ sl.CombineRange_Bytes(buf, epic.MetadataLen, len(buf), writePerm)
		// @ fold acc(p.ScionPath.Base.Mem(), R1)
		// @ fold acc(p.ScionPath.Mem(ubuf[epic.MetadataLen:]), R1)
		// @ fold acc(p.Mem(ubuf), R1)
		return nil
	case *onehop.Path:
		// Zero out IF.SegID
		// @ unfold sl.Bytes(buf, 0, len(buf))
		// @ assert forall j int :: { &buf[2:][j] } 0 <= 2 ==> &buf[2:][j] == &buf[2 + j]
		binary.BigEndian.PutUint16(buf[2:], 0)
		// Zero out HF.Flags&&Alerts
		buf[8] = 0
		// Zero out second HF
		// @ assert forall j int :: { &buf[20:][j] } 0 <= 12 ==> &buf[20:][j] == &buf[20 + j]
		copy(buf[20:], []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0} /*@ , R20 @*/)
		// @ fold sl.Bytes(buf, 0, len(buf))
		return nil
	default:
		return serrors.New(fmt.Sprintf("unknown path type %T", orig))
	}
}

// @ requires  len(buf) >= MACBufferSize - epic.MetadataLen
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
		// @ assert forall j int :: { &buf[offset+2:][j] } 0 <= j && j < len(buf[offset+2:]) ==>
		// @ 	&buf[offset+2:][j] == &buf[offset+2+j]
		binary.BigEndian.PutUint16(buf[offset+2:], 0)
		// @ fold sl.Bytes(buf, 0, len(buf))
		offset += 8
	}
	// @ invariant base.WeaklyValid()
	// @ invariant 0 <= i && i <= base.NumINF
	// @ invariant 4 <= offset && offset <= 28 + base.NumINF * 12 * scion.MaxHops
	// @ invariant i == 0 ==> offset == old(offset)
	// @ invariant i > 0 ==> offset == old(offset) + 12 * int(base.PathMeta.SegLen[i-1])
	// @ invariant sl.Bytes(buf, 0, len(buf))
	// @ decreases base.NumINF - i
	for i := 0; i < base.NumINF; i++ {
		// @ invariant base.WeaklyValid()
		// @ invariant i < base.NumINF
		// @ invariant 0 <= j && j <= int(base.PathMeta.SegLen[i])
		// @ invariant offset == old(offset) + 12 * j
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
	// @ fold sl.Bytes(buf, 0, len(buf))
}

// @ requires len(b) >= 6
// @ preserves acc(&b[0]) && acc(&b[1]) && acc(&b[2]) && acc(&b[3]) && acc(&b[4]) && acc(&b[5])
// @ decreases
func bigEndianPutUint48(b []byte, v uint64) {
	b[0] = byte(v >> 40)
	b[1] = byte(v >> 32)
	//@ assert forall j int :: { &b[2:6][j] } 0 <= 4 ==> &b[2:6][j] == &b[2 + j]
	binary.BigEndian.PutUint32(b[2:6], uint32(v))
}
