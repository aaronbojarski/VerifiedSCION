// Code generated by protoc-gen-connect-go. DO NOT EDIT.
//
// Source: proto/control_plane/v1/cppki.proto

package control_planeconnect

import (
	connect "connectrpc.com/connect"
	context "context"
	errors "errors"
	control_plane "github.com/scionproto/scion/pkg/proto/control_plane"
	http "net/http"
	strings "strings"
)

// This is a compile-time assertion to ensure that this generated file and the connect package are
// compatible. If you get a compiler error that this constant is not defined, this code was
// generated with a version of connect newer than the one compiled into your binary. You can fix the
// problem by either regenerating this code with an older version of connect or updating the connect
// version compiled into your binary.
const _ = connect.IsAtLeastVersion1_13_0

const (
	// TrustMaterialServiceName is the fully-qualified name of the TrustMaterialService service.
	TrustMaterialServiceName = "proto.control_plane.v1.TrustMaterialService"
)

// These constants are the fully-qualified names of the RPCs defined in this package. They're
// exposed at runtime as Spec.Procedure and as the final two segments of the HTTP route.
//
// Note that these are different from the fully-qualified method names used by
// google.golang.org/protobuf/reflect/protoreflect. To convert from these constants to
// reflection-formatted method names, remove the leading slash and convert the remaining slash to a
// period.
const (
	// TrustMaterialServiceChainsProcedure is the fully-qualified name of the TrustMaterialService's
	// Chains RPC.
	TrustMaterialServiceChainsProcedure = "/proto.control_plane.v1.TrustMaterialService/Chains"
	// TrustMaterialServiceTRCProcedure is the fully-qualified name of the TrustMaterialService's TRC
	// RPC.
	TrustMaterialServiceTRCProcedure = "/proto.control_plane.v1.TrustMaterialService/TRC"
)

// These variables are the protoreflect.Descriptor objects for the RPCs defined in this package.
var (
	trustMaterialServiceServiceDescriptor      = control_plane.File_proto_control_plane_v1_cppki_proto.Services().ByName("TrustMaterialService")
	trustMaterialServiceChainsMethodDescriptor = trustMaterialServiceServiceDescriptor.Methods().ByName("Chains")
	trustMaterialServiceTRCMethodDescriptor    = trustMaterialServiceServiceDescriptor.Methods().ByName("TRC")
)

// TrustMaterialServiceClient is a client for the proto.control_plane.v1.TrustMaterialService
// service.
type TrustMaterialServiceClient interface {
	Chains(context.Context, *connect.Request[control_plane.ChainsRequest]) (*connect.Response[control_plane.ChainsResponse], error)
	TRC(context.Context, *connect.Request[control_plane.TRCRequest]) (*connect.Response[control_plane.TRCResponse], error)
}

// NewTrustMaterialServiceClient constructs a client for the
// proto.control_plane.v1.TrustMaterialService service. By default, it uses the Connect protocol
// with the binary Protobuf Codec, asks for gzipped responses, and sends uncompressed requests. To
// use the gRPC or gRPC-Web protocols, supply the connect.WithGRPC() or connect.WithGRPCWeb()
// options.
//
// The URL supplied here should be the base URL for the Connect or gRPC server (for example,
// http://api.acme.com or https://acme.com/grpc).
func NewTrustMaterialServiceClient(httpClient connect.HTTPClient, baseURL string, opts ...connect.ClientOption) TrustMaterialServiceClient {
	baseURL = strings.TrimRight(baseURL, "/")
	return &trustMaterialServiceClient{
		chains: connect.NewClient[control_plane.ChainsRequest, control_plane.ChainsResponse](
			httpClient,
			baseURL+TrustMaterialServiceChainsProcedure,
			connect.WithSchema(trustMaterialServiceChainsMethodDescriptor),
			connect.WithClientOptions(opts...),
		),
		tRC: connect.NewClient[control_plane.TRCRequest, control_plane.TRCResponse](
			httpClient,
			baseURL+TrustMaterialServiceTRCProcedure,
			connect.WithSchema(trustMaterialServiceTRCMethodDescriptor),
			connect.WithClientOptions(opts...),
		),
	}
}

// trustMaterialServiceClient implements TrustMaterialServiceClient.
type trustMaterialServiceClient struct {
	chains *connect.Client[control_plane.ChainsRequest, control_plane.ChainsResponse]
	tRC    *connect.Client[control_plane.TRCRequest, control_plane.TRCResponse]
}

// Chains calls proto.control_plane.v1.TrustMaterialService.Chains.
func (c *trustMaterialServiceClient) Chains(ctx context.Context, req *connect.Request[control_plane.ChainsRequest]) (*connect.Response[control_plane.ChainsResponse], error) {
	return c.chains.CallUnary(ctx, req)
}

// TRC calls proto.control_plane.v1.TrustMaterialService.TRC.
func (c *trustMaterialServiceClient) TRC(ctx context.Context, req *connect.Request[control_plane.TRCRequest]) (*connect.Response[control_plane.TRCResponse], error) {
	return c.tRC.CallUnary(ctx, req)
}

// TrustMaterialServiceHandler is an implementation of the
// proto.control_plane.v1.TrustMaterialService service.
type TrustMaterialServiceHandler interface {
	Chains(context.Context, *connect.Request[control_plane.ChainsRequest]) (*connect.Response[control_plane.ChainsResponse], error)
	TRC(context.Context, *connect.Request[control_plane.TRCRequest]) (*connect.Response[control_plane.TRCResponse], error)
}

// NewTrustMaterialServiceHandler builds an HTTP handler from the service implementation. It returns
// the path on which to mount the handler and the handler itself.
//
// By default, handlers support the Connect, gRPC, and gRPC-Web protocols with the binary Protobuf
// and JSON codecs. They also support gzip compression.
func NewTrustMaterialServiceHandler(svc TrustMaterialServiceHandler, opts ...connect.HandlerOption) (string, http.Handler) {
	trustMaterialServiceChainsHandler := connect.NewUnaryHandler(
		TrustMaterialServiceChainsProcedure,
		svc.Chains,
		connect.WithSchema(trustMaterialServiceChainsMethodDescriptor),
		connect.WithHandlerOptions(opts...),
	)
	trustMaterialServiceTRCHandler := connect.NewUnaryHandler(
		TrustMaterialServiceTRCProcedure,
		svc.TRC,
		connect.WithSchema(trustMaterialServiceTRCMethodDescriptor),
		connect.WithHandlerOptions(opts...),
	)
	return "/proto.control_plane.v1.TrustMaterialService/", http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case TrustMaterialServiceChainsProcedure:
			trustMaterialServiceChainsHandler.ServeHTTP(w, r)
		case TrustMaterialServiceTRCProcedure:
			trustMaterialServiceTRCHandler.ServeHTTP(w, r)
		default:
			http.NotFound(w, r)
		}
	})
}

// UnimplementedTrustMaterialServiceHandler returns CodeUnimplemented from all methods.
type UnimplementedTrustMaterialServiceHandler struct{}

func (UnimplementedTrustMaterialServiceHandler) Chains(context.Context, *connect.Request[control_plane.ChainsRequest]) (*connect.Response[control_plane.ChainsResponse], error) {
	return nil, connect.NewError(connect.CodeUnimplemented, errors.New("proto.control_plane.v1.TrustMaterialService.Chains is not implemented"))
}

func (UnimplementedTrustMaterialServiceHandler) TRC(context.Context, *connect.Request[control_plane.TRCRequest]) (*connect.Response[control_plane.TRCResponse], error) {
	return nil, connect.NewError(connect.CodeUnimplemented, errors.New("proto.control_plane.v1.TrustMaterialService.TRC is not implemented"))
}
