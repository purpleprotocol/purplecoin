use super::{
    payload::{PeerInfoRequest, PeerInfoResponse},
    PeerInfoRequestProtocol,
};
use async_trait::async_trait;
use futures::AsyncWriteExt;
use libp2p::{
    core::upgrade::{read_length_prefixed, write_length_prefixed},
    request_response,
};
use std::io;

#[derive(Clone, Debug, Default)]
pub struct PeerInfoRequestCodec;

#[async_trait]
impl request_response::Codec for PeerInfoRequestCodec {
    type Protocol = PeerInfoRequestProtocol;
    type Request = PeerInfoRequest;
    type Response = PeerInfoResponse;

    async fn read_request<T>(&mut self, _: &Self::Protocol, io: &mut T) -> io::Result<Self::Request>
    where
        T: futures::AsyncRead + Unpin + Send,
    {
        let buf = read_length_prefixed(io, 1_000_000).await?;
        if buf.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "empty request".to_string(),
            ));
        }

        let (request, _): (PeerInfoRequest, usize) =
            bincode::decode_from_slice(&buf, bincode::config::standard())
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))?;

        Ok(request)
    }

    async fn read_response<T>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
    ) -> io::Result<Self::Response>
    where
        T: futures::AsyncRead + Unpin + Send,
    {
        let buf = read_length_prefixed(io, 1_000_000).await?;
        if buf.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "empty response".to_string(),
            ));
        }

        let (response, _): (PeerInfoResponse, usize) =
            bincode::decode_from_slice(&buf, bincode::config::standard())
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))?;

        Ok(response)
    }

    async fn write_request<T>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
        req: Self::Request,
    ) -> io::Result<()>
    where
        T: futures::AsyncWrite + Unpin + Send,
    {
        let mut buf = [0u8; 256];
        let req_encoded = bincode::encode_into_slice(&req, &mut buf, bincode::config::standard())
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))?;
        write_length_prefixed(io, buf).await?;
        io.close().await?;

        Ok(())
    }

    async fn write_response<T>(
        &mut self,
        protocol: &Self::Protocol,
        io: &mut T,
        res: Self::Response,
    ) -> io::Result<()>
    where
        T: futures::AsyncWrite + Unpin + Send,
    {
        let mut buf = [0u8; 256];
        let res_encoded = bincode::encode_into_slice(&res, &mut buf, bincode::config::standard())
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))?;
        write_length_prefixed(io, buf).await?;
        io.close().await?;

        Ok(())
    }
}
