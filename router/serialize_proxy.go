// Copyright 2024 SCION Association
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

package router

import (
	"github.com/gopacket/gopacket"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
)

// serializeProxy implements gopacket.SerializeBuffer. It is a very simple implementation that
// writes to a separately allocated buffer (such as a packet's raw buffer). Space is added to the
// buffer via PrependBytes and AppendBytes simply by changing the starting point and length of the
// data slice. No reallocation is ever performed. Running out of append or prepend space triggers a
// panic. It is designed to be a local variable, so New() returns a value. The entire buffer
// underpinning the given slice may be used; that is, from the start up to the remaining capacity.
type serializeProxy struct {

	// The slice's offset can't be changed as that is irreversible.
	// So we keep track of the prepend point separately from the slice.

	restart int // the value to reset start to during Clear().
	start   int // current start of the useful data in the buffer.
	data    []byte
	layers  []gopacket.LayerType
}

// newSerializeProxy returns a new serializeProxy. The initial prepend/append point is set to the
// end of the buffer in anticipation of AppendBytes never being used. The prepend/append point can
// be changed when calling clear().
// @ requires acc(buf)
// @ decreases
func newSerializeProxy(buf []byte) serializeProxy {
	return newSerializeProxyStart(buf, cap(buf))
}

// newSerializeProxyStart returns a new serializeProxy. The initial prepend/append point is set to
// the given start value. This has the same effect as calling clear(statr).
// @ requires acc(buf)
// @ requires 0 <= start && start <= cap(buf)
// @ decreases
func newSerializeProxyStart(buf []byte, start int) (res serializeProxy) {
	serBuf /*@@@*/ := serializeProxy{
		data: buf,
	}
	// @ fold serBuf.NonInitMem()
	serBuf.clear(start)
	return serBuf
}

// Resets the buffer to empty and sets the initial prepend/append point to the given position.
// The next prepend will claim an area ending with index newStart - 1. The next append will claim an
// area starting with index newStart.
// @ requires s.NonInitMem()
// @ requires 0 <= newStart && newStart <= s.getDataCap()
// @ decreases
func (s *serializeProxy) clear(newStart int) {
	// @ unfold s.NonInitMem()
	s.restart = newStart
	s.start = newStart
	// @ sl.AssertSliceOverlap(s.data, 0, newStart)
	s.data = s.data[:newStart]
	s.layers = s.layers[:0]
	// @ fold s.Mem()
}

// Implements serializeBuffer.Clear(). This implementation never returns an error.
// The initial prepend/append point is reset to that which was set by the last call to clear().
// @ requires s.Mem()
// @ decreases
func (s *serializeProxy) Clear() error {
	// @ unfold s.Mem()
	restart := s.restart
	// @ fold s.Mem()
	s.clear(restart)
	return nil
}

// PrependBytes implements serializeBuffer.PrependBytes(). It never returns an error.
// It can panic if attenpting to prepend before the start of the buffer.
// @ requires s.Mem()
// @ requires 0 <= num && num <= s.getStart()
// @ decreases
func (s *serializeProxy) PrependBytes(num int) ([]byte, error) {
	// @ unfold s.Mem()
	// @ defer fold s.Mem()
	s.start -= num
	// @ sl.AssertSliceOverlap(s.data, s.start, s.start+num)
	return s.data[s.start : s.start+num], nil
}

// AppendBytes implements serializeBuffer.AppendBytes(). It never returns an error.
// It can panic if attempting to append past the end of the buffer.
// @ requires s.Mem()
// @ requires 0 <= num
// @ decreases
func (s *serializeProxy) AppendBytes(num int) ([]byte, error) {
	// @ unfold s.Mem()
	// @ defer fold s.Mem()
	ol := len(s.data)
	nl := ol + num
	// @ sl.AssertSliceOverlap(s.data, 0, nl)
	s.data = s.data[:nl]
	// @ sl.AssertSliceOverlap(s.data, ol, nl)
	return s.data[ol:nl], nil
}

// Bytes implements serializeBuffer.Bytes(). It returns a slice that represents the useful portion
// of the buffer. That is the portion that contains all the prepended and appended bytes since the
// last call to Clear().
// @ requires s.Mem()
// @ decreases
func (s *serializeProxy) Bytes() []byte {
	// @ unfold s.Mem()
	// @ defer fold s.Mem()
	// @ sl.AssertSliceOverlap(s.data, s.start, len(s.data))
	return s.data[s.start:]
}

// Bytes implements serializeBuffer.Layers.
// @ requires s.Mem()
func (s *serializeProxy) Layers() []gopacket.LayerType {
	// @ unfold s.Mem()
	// @ defer fold s.Mem()
	return s.layers
}

// Bytes implements serializeBuffer.PushLayer.
// @ requires s.Mem()
func (s *serializeProxy) PushLayer(l gopacket.LayerType) {
	// @ unfold s.Mem()
	// @ lenLayers := len(s.layers)
	s.layers = append( /*@ R00, @*/ s.layers, l)
	// @ assert s.layers[lenLayers] === l
	// @ fold s.Mem()
}
