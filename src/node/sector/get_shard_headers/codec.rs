use super::{
    payload::{GetShardHeaderRequest, GetShardHeaderResponse},
    GetShardHeaderRequestProtocol,
};
use async_trait::async_trait;
use bincode::enc::write::SliceWriter;
use futures::AsyncWriteExt;
use libp2p::{
    core::upgrade::{read_length_prefixed, write_length_prefixed},
    request_response,
};
use std::io;

const REQUEST_BUF_SIZE: usize = 256;
const RESPONSE_BUF_SIZE: usize = 10_000;

#[derive(Clone, Debug, Default)]
pub struct GetShardHeaderRequestCodec;

#[async_trait]
impl request_response::Codec for GetShardHeaderRequestCodec {
    type Protocol = GetShardHeaderRequestProtocol;
    type Request = GetShardHeaderRequest;
    type Response = GetShardHeaderResponse;

    async fn read_request<T>(&mut self, _: &Self::Protocol, io: &mut T) -> io::Result<Self::Request>
    where
        T: futures::AsyncRead + Unpin + Send,
    {
        let buf = read_length_prefixed(io, REQUEST_BUF_SIZE).await?;
        if buf.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "empty request".to_string(),
            ));
        }

        let (request, _): (GetShardHeaderRequest, usize) = crate::codec::decode(&buf)
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
        let buf = read_length_prefixed(io, RESPONSE_BUF_SIZE).await?;
        if buf.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "empty response".to_string(),
            ));
        }

        let (response, _): (GetShardHeaderResponse, usize) = crate::codec::decode(&buf)
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
        let mut buf = [0u8; REQUEST_BUF_SIZE];
        let mut writer = SliceWriter::new(&mut buf);
        let req_encoded = crate::codec::encode(&mut writer, &req)
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
        let mut buf = [0u8; RESPONSE_BUF_SIZE];
        let mut writer = SliceWriter::new(&mut buf);
        let res_encoded = crate::codec::encode(&mut writer, &res)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))?;
        write_length_prefixed(io, buf).await?;
        io.close().await?;

        Ok(())
    }
}
