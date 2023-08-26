// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

#![feature(stmt_expr_attributes)]
#![allow(unreachable_code)]

use log::*;
use mimalloc::MiMalloc;
use purplecoin::chain::backend::disk::DiskBackend;
use purplecoin::chain::*;
use purplecoin::global::*;
use purplecoin::node::*;
use purplecoin::primitives::*;
use purplecoin::settings::SETTINGS;

use std::env;
use std::sync::atomic::Ordering;
use std::thread;
use std::time::Duration;
use tarpc::server::{self, Channel};
use tokio::runtime::Builder;
use tokio::time::sleep;
use tracing_subscriber::prelude::*;
use triomphe::Arc;

#[cfg(not(windows))]
use signal_hook::consts::signal::*;
#[cfg(not(windows))]
use signal_hook::consts::TERM_SIGNALS;
#[cfg(not(windows))]
use signal_hook::flag;
#[cfg(not(windows))]
use signal_hook::iterator::Signals;

use warp::Filter;

#[cfg(feature = "blake3sum")]
use blake3::Hasher as Blake3;
#[cfg(feature = "gui")]
use iced::window::icon::Icon;
#[cfg(feature = "gui")]
use iced::{Application, Settings};
#[cfg(feature = "gui")]
use purplecoin::gui::GUI;
#[cfg(feature = "sha256sum")]
use sha2::{Digest, Sha256};
#[cfg(feature = "gui")]
use std::process;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() -> anyhow::Result<()> {
    purplecoin::global::init();

    #[cfg(not(windows))]
    for sig in TERM_SIGNALS {
        // When terminated by a second term signal, exit with exit code 1.
        // This will do nothing the first time (because term_now is false).
        flag::register_conditional_shutdown(*sig, 1, EXIT_SIGNAL.clone())?;
        // But this will "arm" the above for the second time, by setting it to true.
        // The order of registering these is important, if you put this one first, it will
        // first arm and then terminate ‒ all in the first round.
        flag::register(*sig, EXIT_SIGNAL.clone())?;
    }

    run_init()
}

fn run_init() -> anyhow::Result<()> {
    #[cfg(feature = "gui")]
    thread::spawn(start_runtime);

    #[cfg(not(feature = "gui"))]
    let t = thread::spawn(start_runtime);

    purplecoin::wallet::load_wallets();

    #[cfg(not(feature = "gui"))]
    {
        // This loop runs forever, and blocks until the exit signal is received
        loop {
            if EXIT_SIGNAL.load(Ordering::Relaxed) {
                break;
            }
            thread::sleep(Duration::from_millis(200));
        }

        // Wait for thread to exit
        let _ = t.join().unwrap();
    }

    #[cfg(feature = "gui")]
    start_gui()?;

    Ok(())
}

fn start_runtime() -> anyhow::Result<()> {
    let db = purplecoin::chain::backend::create_rocksdb_backend();
    let config = ChainConfig::new(&SETTINGS.node.network_name);
    let disk_backend =
        DiskBackend::new(db, Arc::new(config.clone()), None, None, None, None).unwrap();
    let chain = Chain::new(disk_backend, &config);
    let worker_threads = if SETTINGS.node.network_threads == 0 {
        num_cpus::get()
    } else {
        SETTINGS.node.network_threads as usize
    };

    let verifier_threads = if SETTINGS.node.verifier_threads == 0 {
        num_cpus::get()
    } else {
        SETTINGS.node.verifier_threads as usize
    };

    // Also set rayon thread count according to verifier_threads value
    rayon::ThreadPoolBuilder::new()
        .num_threads(verifier_threads)
        .build_global()
        .unwrap();

    let runtime = Builder::new_multi_thread()
        .max_blocking_threads(verifier_threads)
        .worker_threads(worker_threads)
        .enable_io()
        .enable_time()
        .build()
        .unwrap();

    runtime.block_on(async {
        init_tracing("PurplecoinCore").unwrap();
        perform_sanity_checks();
        let mut node = Node::new(chain.clone());

        if SETTINGS.node.memory_only {
            info!(
                "Running Purplecoin Core v{} on {} in memory only mode",
                env!("CARGO_PKG_VERSION"),
                SETTINGS.node.network_name
            );
        } else {
            info!(
                "Running Purplecoin Core v{} on {}",
                env!("CARGO_PKG_VERSION"),
                SETTINGS.node.network_name
            );
        }

        #[cfg(feature = "rpc")]
        let run_rpc = async move {
            if SETTINGS.network.rpc_enabled {
                // Create transports
                let (client_transport, server_transport) = tarpc::transport::channel::unbounded();
                let server = server::BaseChannel::with_defaults(server_transport);
                let client = RpcServerDefinitionClient::new(
                    tarpc::client::Config::default(),
                    client_transport,
                )
                .spawn();

                // Schedule rpc server
                tokio::spawn(server.execute(RpcServer { chain }.serve()));

                // Set up http route
                let client_filter = warp::any().map(move || client.clone());
                let rpc_path = warp::post()
                    .and(warp::path::end())
                    .and(json_body())
                    .and(client_filter.clone())
                    .and(warp::header("authorization"))
                    .and_then(handle_rpc_request);

                let port = match SETTINGS.node.network_name.as_str() {
                    "mainnet" => SETTINGS.network.rpc_listen_port_mainnet,
                    "testnet" => SETTINGS.network.rpc_listen_port_testnet,
                    "devnet" => SETTINGS.network.rpc_listen_port_devnet,
                    other => panic!("Invalid network name: {other}"),
                };

                info!(
                    "Purplecoin Core v{} RPC Listening on port {}",
                    env!("CARGO_PKG_VERSION"),
                    port
                );

                warp::serve(rpc_path).run(([127, 0, 0, 1], port)).await;
            } else {
                loop {
                    sleep(Duration::from_secs(1)).await;
                }
            }

            Ok::<(), ()>(())
        };

        #[cfg(not(feature = "rpc"))]
        let run_rpc = async move {
            loop {
                sleep(Duration::from_secs(1)).await;
            }

            Ok::<(), ()>(())
        };

        tokio::select!(
            _ = tokio::spawn(run_rpc) => (),
            _ = tokio::spawn(run_periodics()) => (),
            _ = tokio::spawn(check_exit_signal()) => (),
            _ = node.bootstrap_then_run() => (),
        );

        // TODO: Cleanup anything here

        #[cfg(feature = "gui")]
        // When we run the GUI we must terminate it this way
        process::exit(1);

        Ok(())
    })
}

async fn check_exit_signal() {
    loop {
        if EXIT_SIGNAL.load(Ordering::Relaxed) {
            break;
        }

        #[cfg(not(windows))]
        let mut signals = Signals::new(TERM_SIGNALS).unwrap();

        #[cfg(not(windows))]
        if let Some(signal) = signals.pending().next() {
            match signal {
                SIGINT => {
                    break;
                }
                SIGTERM => {
                    break;
                }
                term_sig => {
                    debug!("Received termination signal: {}", term_sig);
                    break;
                }
            }
        }

        sleep(Duration::from_millis(10)).await;
    }

    info!(
        "Purplecoin Core v{} shutting down...",
        env!("CARGO_PKG_VERSION")
    )
}

#[cfg(feature = "gui")]
fn start_gui() -> iced::Result {
    let mut gui_settings = Settings {
        id: Some("org.purplecoin.PurplecoinCore".to_owned()),
        ..Settings::default()
    };

    // Set application icon
    {
        gui_settings.window.icon = Some(
            Icon::from_rgba(
                purplecoin::global::LOGO_PIXELS.0.clone(),
                purplecoin::global::LOGO_PIXELS.1,
                purplecoin::global::LOGO_PIXELS.2,
            )
            .unwrap(),
        );
    }

    // Don't close application implicitly when clicking the close window button
    #[cfg(target_os = "macos")]
    {
        gui_settings.exit_on_close_request = false;
    }

    info!(
        "Starting Purplecoin Core v{} GUI",
        env!("CARGO_PKG_VERSION")
    );
    GUI::run(gui_settings)
}

/// Schedules periodic jobs such as chain pruning
async fn run_periodics() -> anyhow::Result<()> {
    loop {
        sleep(Duration::from_millis(1)).await;
    }

    Ok(())
}

async fn handle_rpc_request(
    request: tarpc::Request<RpcServerDefinitionRequest>,
    client: RpcServerDefinitionClient,
    authorization: String,
) -> Result<impl warp::Reply, warp::Rejection> {
    if !check_authorization_header(authorization) {
        return Ok(warp::reply::with_status(
            warp::reply::json(&"Forbidden".to_owned()),
            warp::http::status::StatusCode::FORBIDDEN,
        ));
    }

    match dispatch_rpc_request(request, client).await {
        Ok(resp) => Ok(warp::reply::with_status(
            warp::reply::json(&resp),
            warp::http::StatusCode::CREATED,
        )),

        Err(err) => Ok(warp::reply::with_status(
            warp::reply::json(&err),
            warp::http::StatusCode::BAD_REQUEST,
        )),
    }
}

fn check_authorization_header(auth: String) -> bool {
    let split: Vec<_> = auth.split(' ').collect();

    if split.len() != 2 {
        return false;
    }

    if split[0] != "Basic" {
        return false;
    }

    let decoded = match base64::decode(split[1]) {
        Ok(decoded) => decoded,
        Err(_) => return false,
    };

    // Hash both stored credentials and given ones and then constant compare the two hashes
    let hash_key = "purplecoin.basic_auth";
    let oracle_key = format!(
        "{}:{}",
        SETTINGS.network.rpc_username, SETTINGS.network.rpc_password
    );
    let oracle_hash = Hash256::hash_from_slice(oracle_key.as_bytes(), hash_key);
    let hash = Hash256::hash_from_slice(decoded, hash_key);

    constant_time_eq::constant_time_eq_32(&oracle_hash.0, &hash.0)
}

/// Initializes an OpenTelemetry tracing subscriber with a Jaeger backend.
fn init_tracing(service_name: &str) -> anyhow::Result<()> {
    env::set_var("OTEL_BSP_MAX_EXPORT_BATCH_SIZE", "12");
    let tracer = opentelemetry_jaeger::new_pipeline()
        .with_service_name(service_name)
        .with_max_packet_size(2usize.pow(13))
        .install_batch(opentelemetry::runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::filter::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .try_init()?;

    Ok(())
}

fn json_body(
) -> impl Filter<Extract = (tarpc::Request<RpcServerDefinitionRequest>,), Error = warp::Rejection> + Clone
{
    // When accepting a body, we want a JSON body
    // (and to reject huge payloads)...
    warp::body::content_length_limit(1024 * 64)
        .and(warp::body::json::<tarpc::Request<RpcServerDefinitionRequest>>())
}

fn perform_sanity_checks() {
    // Verify addresses checksums
    let addresses_mainnet_filename = pub_addresses_file_mainnet();
    let addresses_testnet_filename = pub_addresses_file_testnet();
    verify_addresses_checksum(addresses_mainnet_filename, ADDRESSES_RAW_MAINNET);
    verify_addresses_checksum(addresses_testnet_filename, ADDRESSES_RAW_TESTNET);

    // Validate settings
    SETTINGS.validate();

    // Add here more sanity checks
}

fn verify_addresses_checksum(addresses_path: &str, addresses_raw: &str) {
    let mut addresses_path_split: Vec<_> = addresses_path.split('.').collect();
    if !addresses_path.contains("genesisbalances") {
        panic!("Invalid addresses path");
    }

    if addresses_path_split.len() < 4 {
        panic!("invalid addresses path!");
    }

    #[cfg(feature = "blake3sum")]
    let sumtype = "blake3";

    #[cfg(feature = "sha256sum")]
    let sumtype = "sha256";

    addresses_path_split.pop().unwrap();
    let oracle_checksum = addresses_path_split
        .iter()
        .find(|nibble| nibble.contains(sumtype))
        .ok_or("addresses file name doesn't contain a checksum")
        .unwrap()
        .to_owned()
        .split('_')
        .collect::<Vec<_>>()[1];

    info!("Verifying addresses file checksum...");
    {
        #[cfg(feature = "blake3sum")]
        let mut hasher = Blake3::new();

        #[cfg(feature = "sha256sum")]
        let mut hasher = Sha256::new();

        hasher.update(addresses_raw.as_bytes());
        let result = hasher.finalize();

        #[cfg(feature = "blake3sum")]
        let checksum = hex::encode(result.as_bytes());

        #[cfg(feature = "sha256sum")]
        let checksum = hex::encode(result);

        if checksum != oracle_checksum {
            panic!(
                "Addresses file checksum verification failed! Got: {checksum}, Expected: {oracle_checksum}"
            );
        }
    }
    info!("Checksum verification passed!");
}
