// Copyright © 2017–2022 Trevor Spiteri

// Copying and distribution of this file, with or without
// modification, are permitted in any medium without royalty provided
// the copyright notice and this notice are preserved. This file is
// offered as-is, without any warranty.

// Notes:
//
//  1. Configure GMP with --enable-fat so that built file is portable.
//
//  2. Configure GMP, MPFR and MPC with: --disable-shared --with-pic
//
//  3. Add symlinks to work around relative path issues in MPFR and MPC.
//     In MPFR: ln -s ../gmp-build
//     In MPC: ln -s ../mpfr-src ../mpfr-build ../gmp-build .
//
//  4. Unset CC and CFLAGS before building MPFR, so that both MPFR and MPC are
//     left to their default behavior and obtain them from gmp.h.
//
//  5. Use relative paths for configure otherwise msys/mingw might be
//     confused with drives and such.

#[cfg(unix)]
use std::os::unix::fs as unix_fs;
#[cfg(windows)]
use std::os::windows::fs as windows_fs;
use std::{
    cmp::Ordering,
    env,
    ffi::{OsStr, OsString},
    fs::{self, File},
    io::{BufRead, BufReader, BufWriter, Result as IoResult, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    str,
};

const GMP_DIR: &str = "gmp-6.2.1-c";
const MPFR_DIR: &str = "mpfr-4.1.0-p13-c";
const MPC_DIR: &str = "mpc-1.2.1-c";
const GMP_VER: (i32, i32, i32) = (6, 2, 1);
const MPFR_VER: (i32, i32, i32) = (4, 1, 0);
const MPC_VER: (i32, i32, i32) = (1, 2, 1);

#[derive(Clone, Copy, PartialEq)]
enum Target {
    Mingw,
    Msvc,
    Other,
}

struct Environment {
    rustc: OsString,
    c_compiler: OsString,
    target: Target,
    cross_target: Option<String>,
    c_no_tests: bool,
    src_dir: PathBuf,
    out_dir: PathBuf,
    lib_dir: PathBuf,
    include_dir: PathBuf,
    build_dir: PathBuf,
    cache_dir: Option<PathBuf>,
    jobs: OsString,
    version_prefix: String,
    version_patch: Option<u64>,
    use_system_libs: bool,
    workaround_47048: Workaround47048,
}

#[derive(Clone, Copy, PartialEq)]
enum Workaround47048 {
    Yes,
    No,
}

fn main() {
    let rustc = cargo_env("RUSTC");
    let cc = env::var_os("CC");
    let cc_cache_dir = cc.as_ref().map(|cc| {
        let mut dir = OsString::from("CC-");
        dir.push(cc);
        dir
    });
    let c_compiler = cc.unwrap_or_else(|| "gcc".into());

    let host = cargo_env("HOST")
        .into_string()
        .expect("env var HOST having sensible characters");
    let raw_target = cargo_env("TARGET")
        .into_string()
        .expect("env var TARGET having sensible characters");
    let force_cross = there_is_env("CARGO_FEATURE_FORCE_CROSS");
    if !force_cross && !compilation_target_allowed(&host, &raw_target) {
        panic!(
            "Cross compilation from {} to {} not supported! \
             Use the `force-cross` feature to cross compile anyway.",
            host, raw_target
        );
    }

    let target = if raw_target.contains("-windows-msvc") {
        Target::Msvc
    } else if raw_target.contains("-windows-gnu") {
        Target::Mingw
    } else {
        Target::Other
    };
    let cross_target = if host == raw_target {
        None
    } else {
        Some(raw_target)
    };

    let c_no_tests = there_is_env("CARGO_FEATURE_C_NO_TESTS");

    let src_dir = PathBuf::from(cargo_env("CARGO_MANIFEST_DIR"));
    let out_dir = PathBuf::from(cargo_env("OUT_DIR"));

    let (version_prefix, version_patch) = get_version();

    println!("cargo:rerun-if-env-changed=GMP_MPFR_SYS_CACHE");
    let cache_dir = match env::var_os("GMP_MPFR_SYS_CACHE") {
        Some(ref c) if c.is_empty() || c == "_" => None,
        Some(c) => Some(PathBuf::from(c)),
        None => system_cache_dir().map(|c| c.join("gmp-mpfr-sys")),
    };
    let cache_target = cross_target.as_ref().unwrap_or(&host);
    let cache_dir = cache_dir
        .map(|cache| cache.join(&version_prefix))
        .map(|cache| cache.join(cache_target))
        .map(|cache| match cc_cache_dir {
            Some(dir) => cache.join(dir),
            None => cache,
        });

    let use_system_libs = there_is_env("CARGO_FEATURE_USE_SYSTEM_LIBS");
    if use_system_libs {
        match target {
            Target::Msvc => panic!("the use-system-libs feature is not supported on this target"),
            Target::Mingw => mingw_pkg_config_libdir_or_panic(),
            _ => {}
        }
    }
    let mut env = Environment {
        rustc,
        c_compiler,
        target,
        cross_target,
        c_no_tests,
        src_dir,
        out_dir: out_dir.clone(),
        lib_dir: out_dir.join("lib"),
        include_dir: out_dir.join("include"),
        build_dir: out_dir.join("build"),
        cache_dir,
        jobs: cargo_env("NUM_JOBS"),
        version_prefix,
        version_patch,
        use_system_libs,
        workaround_47048: Workaround47048::No,
    };
    env.check_feature(
        "extended_key_value_attributes",
        TRY_EXTENDED_KEY_VALUE_ATTRIBUTES,
        None,
    );
    env.check_feature("unsafe_in_unsafe", TRY_UNSAFE_IN_UNSAFE, None);

    // make sure we have target directories
    create_dir_or_panic(&env.lib_dir);
    create_dir_or_panic(&env.include_dir);

    env.workaround_47048 = check_for_bug_47048(&env);

    if env.use_system_libs {
        check_system_libs(&env);
    } else {
        compile_libs(&env);
    }
}

fn check_system_libs(env: &Environment) {
    let build_dir_existed = env.build_dir.exists();
    let try_dir = env.build_dir.join("system_libs");
    remove_dir_or_panic(&try_dir);
    create_dir_or_panic(&try_dir);
    println!("$ cd {:?}", try_dir);

    println!("$ #Check for system GMP");
    create_file_or_panic(&try_dir.join("system_gmp.c"), SYSTEM_GMP_C);

    let mut cmd = Command::new(&env.c_compiler);
    cmd.current_dir(&try_dir)
        .args(&["-fPIC", "system_gmp.c", "-lgmp", "-o", "system_gmp.exe"]);
    execute(cmd);

    cmd = Command::new(try_dir.join("system_gmp.exe"));
    cmd.current_dir(&try_dir);
    execute(cmd);
    process_gmp_header(
        env,
        &try_dir.join("system_gmp.out"),
        Some(&env.out_dir.join("gmp_h.rs")),
    )
    .unwrap_or_else(|e| panic!("{}", e));

    let feature_mpfr = there_is_env("CARGO_FEATURE_MPFR");
    let feature_mpc = there_is_env("CARGO_FEATURE_MPC");

    if feature_mpfr {
        println!("$ #Check for system MPFR");
        create_file_or_panic(&try_dir.join("system_mpfr.c"), SYSTEM_MPFR_C);

        cmd = Command::new(&env.c_compiler);
        cmd.current_dir(&try_dir).args(&[
            "-fPIC",
            "system_mpfr.c",
            "-lmpfr",
            "-lgmp",
            "-o",
            "system_mpfr.exe",
        ]);
        execute(cmd);

        cmd = Command::new(try_dir.join("system_mpfr.exe"));
        cmd.current_dir(&try_dir);
        execute(cmd);
        process_mpfr_header(
            env,
            &try_dir.join("system_mpfr.out"),
            Some(&env.out_dir.join("mpfr_h.rs")),
        )
        .unwrap_or_else(|e| panic!("{}", e));
    }

    if feature_mpc {
        println!("$ #Check for system MPC");
        create_file_or_panic(&try_dir.join("system_mpc.c"), SYSTEM_MPC_C);

        cmd = Command::new(&env.c_compiler);
        cmd.current_dir(&try_dir).args(&[
            "-fPIC",
            "system_mpc.c",
            "-lmpc",
            "-lgmp",
            "-o",
            "system_mpc.exe",
        ]);
        execute(cmd);

        cmd = Command::new(try_dir.join("system_mpc.exe"));
        cmd.current_dir(&try_dir);
        execute(cmd);
        process_mpc_header(
            env,
            &try_dir.join("system_mpc.out"),
            Some(&env.out_dir.join("mpc_h.rs")),
        )
        .unwrap_or_else(|e| panic!("{}", e));
    }

    if !there_is_env("CARGO_FEATURE_CNODELETE") {
        if build_dir_existed {
            let _ = remove_dir(&try_dir);
        } else {
            remove_dir_or_panic(&env.build_dir);
        }
    }

    write_link_info(env, feature_mpfr, feature_mpc);
}

fn compile_libs(env: &Environment) {
    let gmp_ah = (env.lib_dir.join("libgmp.a"), env.include_dir.join("gmp.h"));
    let mpc_ah = if there_is_env("CARGO_FEATURE_MPC") {
        Some((env.lib_dir.join("libmpc.a"), env.include_dir.join("mpc.h")))
    } else {
        None
    };
    let mpfr_ah = if mpc_ah.is_some() || there_is_env("CARGO_FEATURE_MPFR") {
        Some((
            env.lib_dir.join("libmpfr.a"),
            env.include_dir.join("mpfr.h"),
        ))
    } else {
        None
    };

    let NeedCompile {
        gmp: compile_gmp,
        mpfr: compile_mpfr,
        mpc: compile_mpc,
    } = need_compile(env, &gmp_ah, &mpfr_ah, &mpc_ah);
    if compile_gmp {
        check_for_msvc(env);
        remove_dir_or_panic(&env.build_dir);
        create_dir_or_panic(&env.build_dir);
        link_dir(&env.src_dir.join(GMP_DIR), &env.build_dir.join("gmp-src"));
        let (ref a, ref h) = gmp_ah;
        build_gmp(env, a, h);
    }
    if compile_mpfr {
        link_dir(&env.src_dir.join(MPFR_DIR), &env.build_dir.join("mpfr-src"));
        let (ref a, ref h) = *mpfr_ah.as_ref().unwrap();
        build_mpfr(env, a, h);
    }
    if compile_mpc {
        link_dir(&env.src_dir.join(MPC_DIR), &env.build_dir.join("mpc-src"));
        let (ref a, ref h) = *mpc_ah.as_ref().unwrap();
        build_mpc(env, a, h);
    }
    if compile_gmp {
        if !there_is_env("CARGO_FEATURE_CNODELETE") {
            remove_dir_or_panic(&env.build_dir);
        }
        if save_cache(env, &gmp_ah, &mpfr_ah, &mpc_ah) {
            clear_cache_redundancies(env, mpfr_ah.is_some(), mpc_ah.is_some());
        }
    }
    process_gmp_header(env, &gmp_ah.1, Some(&env.out_dir.join("gmp_h.rs")))
        .unwrap_or_else(|e| panic!("{}", e));
    if let Some(ref mpfr_ah) = mpfr_ah {
        process_mpfr_header(env, &mpfr_ah.1, Some(&env.out_dir.join("mpfr_h.rs")))
            .unwrap_or_else(|e| panic!("{}", e));
    }
    if let Some(ref mpc_ah) = mpc_ah {
        process_mpc_header(env, &mpc_ah.1, Some(&env.out_dir.join("mpc_h.rs")))
            .unwrap_or_else(|e| panic!("{}", e));
    }
    write_link_info(env, mpfr_ah.is_some(), mpc_ah.is_some());
}

fn get_version() -> (String, Option<u64>) {
    let version = cargo_env("CARGO_PKG_VERSION")
        .into_string()
        .unwrap_or_else(|e| panic!("version not in utf-8: {:?}", e));
    let last_dot = version
        .rfind('.')
        .unwrap_or_else(|| panic!("version has no dots: {}", version));
    if last_dot == 0 {
        panic!("version starts with dot: {}", version);
    }
    match version[last_dot + 1..].parse::<u64>() {
        Ok(patch) => {
            let mut v = version;
            v.truncate(last_dot);
            (v, Some(patch))
        }
        Err(_) => (version, None),
    }
}

struct NeedCompile {
    gmp: bool,
    mpfr: bool,
    mpc: bool,
}

fn need_compile(
    env: &Environment,
    gmp_ah: &(PathBuf, PathBuf),
    mpfr_ah: &Option<(PathBuf, PathBuf)>,
    mpc_ah: &Option<(PathBuf, PathBuf)>,
) -> NeedCompile {
    let gmp_fine = gmp_ah.0.is_file() && gmp_ah.1.is_file();
    let mpfr_fine = match *mpfr_ah {
        Some((ref a, ref h)) => a.is_file() && h.is_file(),
        None => true,
    };
    let mpc_fine = match *mpc_ah {
        Some((ref a, ref h)) => a.is_file() && h.is_file(),
        None => true,
    };
    if gmp_fine && mpfr_fine && mpc_fine {
        if should_save_cache(env, mpfr_ah.is_some(), mpc_ah.is_some())
            && save_cache(env, gmp_ah, mpfr_ah, mpc_ah)
        {
            clear_cache_redundancies(env, mpfr_ah.is_some(), mpc_ah.is_some());
        }
        return NeedCompile {
            gmp: false,
            mpfr: false,
            mpc: false,
        };
    } else if load_cache(env, gmp_ah, mpfr_ah, mpc_ah) {
        // if loading cache works, we're done
        return NeedCompile {
            gmp: false,
            mpfr: false,
            mpc: false,
        };
    }
    let need_mpc = !mpc_fine;
    let need_mpfr = need_mpc || !mpfr_fine;
    let need_gmp = need_mpfr || !gmp_fine;
    NeedCompile {
        gmp: need_gmp,
        mpfr: need_mpfr,
        mpc: need_mpc,
    }
}

fn save_cache(
    env: &Environment,
    gmp_ah: &(PathBuf, PathBuf),
    mpfr_ah: &Option<(PathBuf, PathBuf)>,
    mpc_ah: &Option<(PathBuf, PathBuf)>,
) -> bool {
    let cache_dir = match env.cache_dir {
        Some(ref s) => s,
        None => return false,
    };
    let version_dir = match env.version_patch {
        None => cache_dir.join(&env.version_prefix),
        Some(patch) => cache_dir.join(format!("{}.{}", env.version_prefix, patch)),
    };
    let mut ok = create_dir(&version_dir).is_ok();
    let dir = if env.c_no_tests {
        let no_tests_dir = version_dir.join("c-no-tests");
        ok = ok && create_dir(&no_tests_dir).is_ok();
        no_tests_dir
    } else {
        version_dir
    };
    let (ref a, ref h) = *gmp_ah;
    ok = ok && copy_file(a, &dir.join("libgmp.a")).is_ok();
    ok = ok && copy_file(h, &dir.join("gmp.h")).is_ok();
    if let Some((ref a, ref h)) = *mpfr_ah {
        ok = ok && copy_file(a, &dir.join("libmpfr.a")).is_ok();
        ok = ok && copy_file(h, &dir.join("mpfr.h")).is_ok();
    }
    if let Some((ref a, ref h)) = *mpc_ah {
        ok = ok && copy_file(a, &dir.join("libmpc.a")).is_ok();
        ok = ok && copy_file(h, &dir.join("mpc.h")).is_ok();
    }
    ok
}

fn clear_cache_redundancies(env: &Environment, mpfr: bool, mpc: bool) {
    let cache_dir = match env.cache_dir {
        Some(ref s) => s,
        None => return,
    };
    let cache_dirs = cache_directories(env, cache_dir)
        .into_iter()
        .rev()
        .filter(|x| match env.version_patch {
            None => x.1.is_none(),
            Some(patch) => x.1.map(|p| p <= patch).unwrap_or(false),
        });
    for (version_dir, version_patch) in cache_dirs {
        let no_tests_dir = version_dir.join("c-no-tests");

        // do not clear newly saved cache
        if version_patch == env.version_patch {
            // but if we tested and c-no-tests directory doesn't have more libs, remove it
            if !env.c_no_tests
                && (mpc || !no_tests_dir.join("libmpc.a").is_file())
                && (mpfr || !no_tests_dir.join("libmpfr.a").is_file())
            {
                let _ = remove_dir(&no_tests_dir);
            }

            continue;
        }

        // Do not clear cache with more libraries than newly saved cache.

        // First check c-no-tests subdirectory for more libs.
        if (!mpc && no_tests_dir.join("libmpc.a").is_file())
            || (!mpfr && no_tests_dir.join("libmpfr.a").is_file())
        {
            continue;
        }
        // Remove c-no-tests subdirectory as it does not have more libs.
        let _ = remove_dir(&no_tests_dir);

        let delete_version_dir_condition = if env.c_no_tests {
            // We did not test, so version_dir must not contain any libs at all.
            !version_dir.join("libgmp.a").is_file()
        } else {
            // We did test, so delete if it does not contain more libs.
            (mpc || !version_dir.join("libmpc.a").is_file())
                && (mpfr || !version_dir.join("libmpfr.a").is_file())
        };
        if delete_version_dir_condition {
            let _ = remove_dir(&version_dir);
        }
    }
}

fn cache_directories(env: &Environment, base: &Path) -> Vec<(PathBuf, Option<u64>)> {
    let dir = match fs::read_dir(base) {
        Ok(dir) => dir,
        Err(_) => return Vec::new(),
    };
    let mut vec = Vec::new();
    for entry in dir {
        let path = match entry {
            Ok(e) => e.path(),
            Err(_) => continue,
        };
        if !path.is_dir() {
            continue;
        }
        let patch = {
            let file_name = match path.file_name() {
                Some(name) => name,
                None => continue,
            };
            let path_str = match file_name.to_str() {
                Some(p) => p,
                None => continue,
            };
            if path_str == env.version_prefix {
                None
            } else if !path_str.starts_with(&env.version_prefix)
                || !path_str[env.version_prefix.len()..].starts_with('.')
            {
                continue;
            } else {
                match path_str[env.version_prefix.len() + 1..].parse::<u64>() {
                    Ok(patch) => Some(patch),
                    Err(_) => continue,
                }
            }
        };
        vec.push((path, patch));
    }
    vec.sort_by_key(|k| k.1);
    vec
}

fn load_cache(
    env: &Environment,
    gmp_ah: &(PathBuf, PathBuf),
    mpfr_ah: &Option<(PathBuf, PathBuf)>,
    mpc_ah: &Option<(PathBuf, PathBuf)>,
) -> bool {
    let cache_dir = match env.cache_dir {
        Some(ref s) => s,
        None => return false,
    };
    let env_version_patch = env.version_patch;
    let cache_dirs = cache_directories(env, cache_dir)
        .into_iter()
        .rev()
        .filter(|x| match env_version_patch {
            None => x.1.is_none(),
            Some(patch) => x.1.map(|p| p >= patch).unwrap_or(false),
        })
        .collect::<Vec<_>>();
    let suffixes: &[Option<&str>] = if env.c_no_tests {
        &[None, Some("c-no-tests")]
    } else {
        // we need tests, so do not try to load from c-no-tests
        &[None]
    };
    for suffix in suffixes {
        for (version_dir, _) in &cache_dirs {
            let joined;
            let dir = if let Some(suffix) = suffix {
                joined = version_dir.join(suffix);
                &joined
            } else {
                version_dir
            };
            let mut ok = true;
            if let Some((ref a, ref h)) = *mpc_ah {
                ok = ok && copy_file(&dir.join("libmpc.a"), a).is_ok();
                let header = dir.join("mpc.h");
                ok = ok && process_mpc_header(env, &header, None).is_ok();
                ok = ok && copy_file(&header, h).is_ok();
            }
            if let Some((ref a, ref h)) = *mpfr_ah {
                ok = ok && copy_file(&dir.join("libmpfr.a"), a).is_ok();
                let header = dir.join("mpfr.h");
                ok = ok && process_mpfr_header(env, &header, None).is_ok();
                ok = ok && copy_file(&header, h).is_ok();
            }
            let (ref a, ref h) = *gmp_ah;
            ok = ok && copy_file(&dir.join("libgmp.a"), a).is_ok();
            let header = dir.join("gmp.h");
            ok = ok && process_gmp_header(env, &header, None).is_ok();
            ok = ok && copy_file(&header, h).is_ok();

            if ok {
                return true;
            }
        }
    }
    false
}

fn should_save_cache(env: &Environment, mpfr: bool, mpc: bool) -> bool {
    let cache_dir = match env.cache_dir {
        Some(ref s) => s,
        None => return false,
    };
    let cache_dirs = cache_directories(env, cache_dir)
        .into_iter()
        .rev()
        .filter(|x| match env.version_patch {
            None => x.1.is_none(),
            Some(patch) => x.1.map(|p| p >= patch).unwrap_or(false),
        })
        .collect::<Vec<_>>();
    let suffixes: &[Option<&str>] = if env.c_no_tests {
        &[None, Some("c-no-tests")]
    } else {
        // we need tests, so do not try to load from c-no-tests
        &[None]
    };
    for suffix in suffixes {
        for (version_dir, _) in &cache_dirs {
            let joined;
            let dir = if let Some(suffix) = suffix {
                joined = version_dir.join(suffix);
                &joined
            } else {
                version_dir
            };
            let mut ok = true;
            if mpc {
                ok = ok && dir.join("libmpc.a").is_file();
                ok = ok && dir.join("mpc.h").is_file();
            }
            if mpfr {
                ok = ok && dir.join("libmpfr.a").is_file();
                ok = ok && dir.join("mpfr.h").is_file();
            }
            ok = ok && dir.join("libgmp.a").is_file();
            ok = ok && dir.join("gmp.h").is_file();
            if ok {
                return false;
            }
        }
    }
    true
}

fn build_gmp(env: &Environment, lib: &Path, header: &Path) {
    let build_dir = env.build_dir.join("gmp-build");
    create_dir_or_panic(&build_dir);
    println!("$ cd {:?}", build_dir);
    let mut conf = String::from("../gmp-src/configure --enable-fat --disable-shared --with-pic");
    if let Some(cross_target) = env.cross_target.as_ref() {
        conf.push_str(" --host ");
        conf.push_str(cross_target);
    }
    configure(&build_dir, &OsString::from(conf));
    make_and_check(env, &build_dir);
    let build_lib = build_dir.join(".libs").join("libgmp.a");
    copy_file_or_panic(&build_lib, lib);
    let build_header = build_dir.join("gmp.h");
    copy_file_or_panic(&build_header, header);
}

fn compatible_version(
    env: &Environment,
    major: i32,
    minor: i32,
    patchlevel: i32,
    expected: (i32, i32, i32),
) -> bool {
    (major == expected.0 && minor >= expected.1)
        && (minor > expected.1 || patchlevel >= expected.2 || env.use_system_libs)
}

fn process_gmp_header(
    env: &Environment,
    header: &Path,
    out_file: Option<&Path>,
) -> Result<(), String> {
    let mut major = None;
    let mut minor = None;
    let mut patchlevel = None;
    let mut limb_bits = None;
    let mut nail_bits = None;
    let mut long_long_limb = None;
    let mut cc = None;
    let mut cflags = None;
    let mut reader = open(header);
    let mut buf = String::new();
    while read_line(&mut reader, &mut buf, header) > 0 {
        let s = "#define __GNU_MP_VERSION ";
        if let Some(start) = buf.find(s) {
            major = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        let s = "#define __GNU_MP_VERSION_MINOR ";
        if let Some(start) = buf.find(s) {
            minor = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        let s = "#define __GNU_MP_VERSION_PATCHLEVEL ";
        if let Some(start) = buf.find(s) {
            patchlevel = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        if buf.contains("#undef _LONG_LONG_LIMB") {
            long_long_limb = Some(false);
        }
        if buf.contains("#define _LONG_LONG_LIMB 1") {
            long_long_limb = Some(true);
        }
        let s = "#define GMP_LIMB_BITS ";
        if let Some(start) = buf.find(s) {
            limb_bits = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        let s = "#define GMP_NAIL_BITS ";
        if let Some(start) = buf.find(s) {
            nail_bits = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        let s = "#define __GMP_CC ";
        if let Some(start) = buf.find(s) {
            cc = Some(
                buf[(start + s.len())..]
                    .trim()
                    .trim_matches('"')
                    .to_string(),
            );
        }
        let s = "#define __GMP_CFLAGS ";
        if let Some(start) = buf.find(s) {
            cflags = Some(
                buf[(start + s.len())..]
                    .trim()
                    .trim_matches('"')
                    .to_string(),
            );
        }
        buf.clear();
    }
    drop(reader);

    let major = major.expect("Cannot determine __GNU_MP_VERSION");
    let minor = minor.expect("Cannot determine __GNU_MP_VERSION_MINOR");
    let patchlevel = patchlevel.expect("Cannot determine __GNU_MP_VERSION_PATCHLEVEL");
    if !compatible_version(env, major, minor, patchlevel, GMP_VER) {
        return Err(format!(
            "This version of gmp-mpfr-sys supports GMP {}.{}.{}, but {}.{}.{} was found",
            GMP_VER.0, GMP_VER.1, GMP_VER.2, major, minor, patchlevel
        ));
    }

    let limb_bits = limb_bits.expect("Cannot determine GMP_LIMB_BITS");
    println!("cargo:limb_bits={}", limb_bits);

    let nail_bits = nail_bits.expect("Cannot determine GMP_NAIL_BITS");
    if nail_bits > 0 {
        println!("cargo:rustc-cfg=nails");
    }

    let long_long_limb = long_long_limb.expect("Cannot determine _LONG_LONG_LIMB");
    let long_long_limb = if long_long_limb {
        println!("cargo:rustc-cfg=long_long_limb");
        "libc::c_ulonglong"
    } else {
        "c_ulong"
    };
    let cc = cc.expect("Cannot determine __GMP_CC");
    let cflags = cflags.expect("Cannot determine __GMP_CFLAGS");

    let content = format!(
        concat!(
            "const GMP_VERSION: c_int = {};\n",
            "const GMP_VERSION_MINOR: c_int = {};\n",
            "const GMP_VERSION_PATCHLEVEL: c_int = {};\n",
            "const GMP_LIMB_BITS: c_int = {};\n",
            "const GMP_NAIL_BITS: c_int = {};\n",
            "type GMP_LIMB_T = {};\n",
            "const GMP_CC: *const c_char = b\"{}\\0\".as_ptr() as _;\n",
            "const GMP_CFLAGS: *const c_char = b\"{}\\0\".as_ptr() as _;\n"
        ),
        major, minor, patchlevel, limb_bits, nail_bits, long_long_limb, cc, cflags
    );
    if let Some(out_file) = out_file {
        let mut rs = create(out_file);
        write_flush(&mut rs, &content, out_file);
    }
    Ok(())
}

fn process_mpfr_header(
    env: &Environment,
    header: &Path,
    out_file: Option<&Path>,
) -> Result<(), String> {
    let mut major = None;
    let mut minor = None;
    let mut patchlevel = None;
    let mut version = None;
    let mut reader = open(header);
    let mut buf = String::new();
    while read_line(&mut reader, &mut buf, header) > 0 {
        let s = "#define MPFR_VERSION_MAJOR ";
        if let Some(start) = buf.find(s) {
            major = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        let s = "#define MPFR_VERSION_MINOR ";
        if let Some(start) = buf.find(s) {
            minor = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        let s = "#define MPFR_VERSION_PATCHLEVEL ";
        if let Some(start) = buf.find(s) {
            patchlevel = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        let s = "#define MPFR_VERSION_STRING ";
        if let Some(start) = buf.find(s) {
            version = Some(
                buf[(start + s.len())..]
                    .trim()
                    .trim_matches('"')
                    .to_string(),
            );
        }
        buf.clear();
    }
    drop(reader);

    let major = major.expect("Cannot determine MPFR_VERSION_MAJOR");
    let minor = minor.expect("Cannot determine MPFR_VERSION_MINOR");
    let patchlevel = patchlevel.expect("Cannot determine MPFR_VERSION_PATCHLEVEL");
    if !compatible_version(env, major, minor, patchlevel, MPFR_VER) {
        return Err(format!(
            "This version of gmp-mpfr-sys supports MPFR {}.{}.{}, but {}.{}.{} was found",
            MPFR_VER.0, MPFR_VER.1, MPFR_VER.2, major, minor, patchlevel
        ));
    }

    let version = version.expect("Cannot determine MPFR_VERSION_STRING");

    let content = format!(
        concat!(
            "const MPFR_VERSION_MAJOR: c_int = {};\n",
            "const MPFR_VERSION_MINOR: c_int = {};\n",
            "const MPFR_VERSION_PATCHLEVEL: c_int = {};\n",
            "const MPFR_VERSION_STRING: *const c_char = b\"{}\\0\".as_ptr() as _;\n"
        ),
        major, minor, patchlevel, version
    );
    if let Some(out_file) = out_file {
        let mut rs = create(out_file);
        write_flush(&mut rs, &content, out_file);
    }
    Ok(())
}

fn process_mpc_header(
    env: &Environment,
    header: &Path,
    out_file: Option<&Path>,
) -> Result<(), String> {
    let mut major = None;
    let mut minor = None;
    let mut patchlevel = None;
    let mut version = None;
    let mut reader = open(header);
    let mut buf = String::new();
    while read_line(&mut reader, &mut buf, header) > 0 {
        let s = "#define MPC_VERSION_MAJOR ";
        if let Some(start) = buf.find(s) {
            major = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        let s = "#define MPC_VERSION_MINOR ";
        if let Some(start) = buf.find(s) {
            minor = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        let s = "#define MPC_VERSION_PATCHLEVEL ";
        if let Some(start) = buf.find(s) {
            patchlevel = buf[(start + s.len())..].trim().parse::<i32>().ok();
        }
        let s = "#define MPC_VERSION_STRING ";
        if let Some(start) = buf.find(s) {
            version = Some(
                buf[(start + s.len())..]
                    .trim()
                    .trim_matches('"')
                    .to_string(),
            );
        }
        buf.clear();
    }
    drop(reader);

    let major = major.expect("Cannot determine MPC_VERSION_MAJOR");
    let minor = minor.expect("Cannot determine MPC_VERSION_MINOR");
    let patchlevel = patchlevel.expect("Cannot determine MPC_VERSION_PATCHLEVEL");
    if !compatible_version(env, major, minor, patchlevel, MPC_VER) {
        return Err(format!(
            "This version of gmp-mpfr-sys supports MPC {}.{}.{}, but {}.{}.{} was found",
            MPC_VER.0, MPC_VER.1, MPC_VER.2, major, minor, patchlevel
        ));
    }

    let version = version.expect("Cannot determine MPC_VERSION_STRING");

    let content = format!(
        concat!(
            "const MPC_VERSION_MAJOR: c_int = {};\n",
            "const MPC_VERSION_MINOR: c_int = {};\n",
            "const MPC_VERSION_PATCHLEVEL: c_int = {};\n",
            "const MPC_VERSION_STRING: *const c_char = b\"{}\\0\".as_ptr() as _;\n"
        ),
        major, minor, patchlevel, version
    );
    if let Some(out_file) = out_file {
        let mut rs = create(out_file);
        write_flush(&mut rs, &content, out_file);
    }
    Ok(())
}

fn build_mpfr(env: &Environment, lib: &Path, header: &Path) {
    let build_dir = env.build_dir.join("mpfr-build");
    create_dir_or_panic(&build_dir);
    println!("$ cd {:?}", build_dir);
    link_dir(
        &env.build_dir.join("gmp-build"),
        &build_dir.join("gmp-build"),
    );

    // unset CC and CFLAGS since both MPFR and MPC will use CC and CFLAGS from gmp.h by default
    println!("$ unset CC CFLAGS");
    std::env::remove_var("CC");
    std::env::remove_var("CFLAGS");

    let mut conf = String::from(
        "../mpfr-src/configure --enable-thread-safe --disable-shared \
         --with-gmp-build=../gmp-build --with-pic",
    );
    if let Some(cross_target) = env.cross_target.as_ref() {
        conf.push_str(" --host ");
        conf.push_str(cross_target);
    }
    configure(&build_dir, &OsString::from(conf));
    make_and_check(env, &build_dir);
    let build_lib = build_dir.join("src").join(".libs").join("libmpfr.a");
    copy_file_or_panic(&build_lib, lib);
    let src_header = env.build_dir.join("mpfr-src").join("src").join("mpfr.h");
    copy_file_or_panic(&src_header, header);
}

fn build_mpc(env: &Environment, lib: &Path, header: &Path) {
    let build_dir = env.build_dir.join("mpc-build");
    create_dir_or_panic(&build_dir);
    println!("$ cd {:?}", build_dir);
    // steal link from mpfr-build to save some copying under MinGW,
    // where a symlink is a just a copy (unless in developer mode).
    mv("../mpfr-build/gmp-build", &build_dir);
    link_dir(&env.build_dir.join("mpfr-src"), &build_dir.join("mpfr-src"));
    link_dir(
        &env.build_dir.join("mpfr-build"),
        &build_dir.join("mpfr-build"),
    );
    let mut conf = String::from(
        "../mpc-src/configure --disable-shared \
         --with-mpfr-include=../mpfr-src/src \
         --with-mpfr-lib=../mpfr-build/src/.libs \
         --with-gmp-include=../gmp-build \
         --with-gmp-lib=../gmp-build/.libs --with-pic",
    );
    if let Some(cross_target) = env.cross_target.as_ref() {
        conf.push_str(" --host ");
        conf.push_str(cross_target);
    }
    configure(&build_dir, &OsString::from(conf));
    make_and_check(env, &build_dir);
    let build_lib = build_dir.join("src").join(".libs").join("libmpc.a");
    copy_file_or_panic(&build_lib, lib);
    let src_header = env.build_dir.join("mpc-src").join("src").join("mpc.h");
    copy_file_or_panic(&src_header, header);
}

fn write_link_info(env: &Environment, feature_mpfr: bool, feature_mpc: bool) {
    let out_str = env.out_dir.to_str().unwrap_or_else(|| {
        panic!(
            "Path contains unsupported characters, can only make {}",
            env.out_dir.display()
        )
    });
    let lib_str = env.lib_dir.to_str().unwrap_or_else(|| {
        panic!(
            "Path contains unsupported characters, can only make {}",
            env.lib_dir.display()
        )
    });
    let include_str = env.include_dir.to_str().unwrap_or_else(|| {
        panic!(
            "Path contains unsupported characters, can only make {}",
            env.include_dir.display()
        )
    });
    println!("cargo:out_dir={}", out_str);
    println!("cargo:lib_dir={}", lib_str);
    println!("cargo:include_dir={}", include_str);
    println!("cargo:rustc-link-search=native={}", lib_str);
    let maybe_static = if env.use_system_libs { "" } else { "static=" };
    if feature_mpc {
        println!("cargo:rustc-link-lib={}mpc", maybe_static);
    }
    if feature_mpfr {
        println!("cargo:rustc-link-lib={}mpfr", maybe_static);
    }
    println!("cargo:rustc-link-lib={}gmp", maybe_static);
    if env.target == Target::Mingw && env.workaround_47048 == Workaround47048::Yes {
        println!("cargo:rustc-link-lib=static=workaround_47048");
    }
}

impl Environment {
    #[allow(dead_code)]
    fn check_feature(&self, name: &str, contents: &str, nightly_features: Option<&str>) {
        let try_dir = self.out_dir.join(format!("try_{}", name));
        let filename = format!("try_{}.rs", name);
        create_dir_or_panic(&try_dir);
        println!("$ cd {:?}", try_dir);

        enum Iteration {
            Stable,
            Unstable,
        }
        for i in &[Iteration::Stable, Iteration::Unstable] {
            let s;
            let file_contents = match *i {
                Iteration::Stable => contents,
                Iteration::Unstable => match nightly_features {
                    Some(features) => {
                        s = format!("#![feature({})]\n{}", features, contents);
                        &s
                    }
                    None => continue,
                },
            };
            create_file_or_panic(&try_dir.join(&filename), file_contents);
            let mut cmd = Command::new(&self.rustc);
            cmd.current_dir(&try_dir)
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .args(&[&*filename, "--emit=dep-info,metadata"]);
            println!("$ {:?} >& /dev/null", cmd);
            let status = cmd
                .status()
                .unwrap_or_else(|_| panic!("Unable to execute: {:?}", cmd));
            if status.success() {
                println!("cargo:rustc-cfg={}", name);
                if let Iteration::Unstable = *i {
                    println!("cargo:rustc-cfg=nightly_{}", name);
                }
                break;
            }
        }

        remove_dir_or_panic(&try_dir);
    }
}

fn cargo_env(name: &str) -> OsString {
    env::var_os(name)
        .unwrap_or_else(|| panic!("environment variable not found: {}, please use cargo", name))
}

fn there_is_env(name: &str) -> bool {
    env::var_os(name).is_some()
}

fn check_for_msvc(env: &Environment) {
    if env.target == Target::Msvc {
        panic!("Windows MSVC target is not supported (linking would fail)");
    }
}

fn rustc_later_eq(major: i32, minor: i32) -> bool {
    let rustc = cargo_env("RUSTC");
    let output = Command::new(rustc)
        .arg("--version")
        .output()
        .expect("unable to run rustc --version");
    let version = String::from_utf8(output.stdout).expect("unrecognized rustc version");
    if !version.starts_with("rustc ") {
        panic!("unrecognized rustc version: {}", version);
    }
    let remain = &version[6..];
    let dot = remain.find('.').expect("unrecognized rustc version");
    let ver_major = remain[0..dot]
        .parse::<i32>()
        .expect("unrecognized rustc version");
    match ver_major.cmp(&major) {
        Ordering::Less => false,
        Ordering::Greater => true,
        Ordering::Equal => {
            let remain = &remain[dot + 1..];
            let dot = remain.find('.').expect("unrecognized rustc version");
            let ver_minor = remain[0..dot]
                .parse::<i32>()
                .expect("unrecognized rustc version");
            ver_minor >= minor
        }
    }
}

fn check_for_bug_47048(env: &Environment) -> Workaround47048 {
    if env.target != Target::Mingw || rustc_later_eq(1, 43) {
        return Workaround47048::No;
    }
    let try_dir = env.build_dir.join("try_47048");
    remove_dir_or_panic(&try_dir);
    create_dir_or_panic(&try_dir);
    println!("$ cd {:?}", try_dir);
    println!("$ #Check for bug 47048");
    create_file_or_panic(&try_dir.join("say_hi.c"), BUG_47048_SAY_HI_C);
    create_file_or_panic(&try_dir.join("c_main.c"), BUG_47048_C_MAIN_C);
    create_file_or_panic(&try_dir.join("r_main.rs"), BUG_47048_R_MAIN_RS);
    create_file_or_panic(&try_dir.join("workaround.c"), BUG_47048_WORKAROUND_C);

    let mut cmd = Command::new(&env.c_compiler);
    cmd.current_dir(&try_dir).args(&["-fPIC", "-c", "say_hi.c"]);
    execute(cmd);

    cmd = Command::new("ar");
    cmd.current_dir(&try_dir)
        .args(&["cr", "libsay_hi.a", "say_hi.o"]);
    execute(cmd);

    cmd = Command::new(&env.c_compiler);
    cmd.current_dir(&try_dir)
        .args(&["c_main.c", "-L.", "-lsay_hi", "-o", "c_main.exe"]);
    execute(cmd);

    // try simple rustc command that should work, so that failure
    // really is the bug being checked for
    cmd = Command::new(&env.rustc);
    cmd.arg("--version");
    execute(cmd);

    cmd = Command::new(&env.rustc);
    cmd.current_dir(&try_dir)
        .args(&["r_main.rs", "-L.", "-lsay_hi", "-o", "r_main.exe"])
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    println!(
        "$ {:?} >& /dev/null && echo Bug 47048 not found || echo Working around bug 47048",
        cmd
    );
    let status = cmd
        .status()
        .unwrap_or_else(|_| panic!("Unable to execute: {:?}", cmd));
    let need_workaround = if status.success() {
        println!("Bug 47048 not found");
        Workaround47048::No
    } else {
        println!("Working around bug 47048");

        cmd = Command::new(&env.c_compiler);
        cmd.current_dir(&try_dir)
            .args(&["-fPIC", "-O2", "-c", "workaround.c"]);
        execute(cmd);

        cmd = Command::new("ar");
        cmd.current_dir(&try_dir)
            .args(&["cr", "libworkaround_47048.a", "workaround.o"]);
        execute(cmd);

        cmd = Command::new(&env.rustc);
        cmd.current_dir(&try_dir).args(&[
            "r_main.rs",
            "-L.",
            "-lsay_hi",
            "-lworkaround_47048",
            "-o",
            "r_main.exe",
        ]);
        execute(cmd);

        let src = try_dir.join("libworkaround_47048.a");
        let dst = env.lib_dir.join("libworkaround_47048.a");
        copy_file_or_panic(&src, &dst);

        Workaround47048::Yes
    };
    remove_dir_or_panic(&try_dir);
    need_workaround
}

fn mingw_pkg_config_libdir_or_panic() {
    let mut cmd = Command::new("pkg-config");
    cmd.args(&["--libs-only-L", "gmp"]);
    let output = execute_stdout(cmd);
    if output.len() < 2 || &output[0..2] != b"-L" {
        panic!("expected pkg-config output to begin with \"-L\"");
    }
    let libdir = str::from_utf8(&output[2..]).expect("output from pkg-config not utf-8");
    println!("cargo:rustc-link-search=native={}", libdir);
}

fn remove_dir(dir: &Path) -> IoResult<()> {
    if !dir.exists() {
        return Ok(());
    }
    assert!(dir.is_dir(), "Not a directory: {:?}", dir);
    println!("$ rm -r {:?}", dir);
    fs::remove_dir_all(dir)
}

fn remove_dir_or_panic(dir: &Path) {
    remove_dir(dir).unwrap_or_else(|_| panic!("Unable to remove directory: {:?}", dir));
}

fn create_dir(dir: &Path) -> IoResult<()> {
    println!("$ mkdir -p {:?}", dir);
    fs::create_dir_all(dir)
}

fn create_dir_or_panic(dir: &Path) {
    create_dir(dir).unwrap_or_else(|_| panic!("Unable to create directory: {:?}", dir));
}

fn create_file_or_panic(filename: &Path, contents: &str) {
    println!("$ printf '%s' {:?}... > {:?}", &contents[0..10], filename);
    let mut file =
        File::create(filename).unwrap_or_else(|_| panic!("Unable to create file: {:?}", filename));
    file.write_all(contents.as_bytes())
        .unwrap_or_else(|_| panic!("Unable to write to file: {:?}", filename));
}

fn copy_file(src: &Path, dst: &Path) -> IoResult<u64> {
    println!("$ cp {:?} {:?}", src, dst);
    fs::copy(src, dst)
}

fn copy_file_or_panic(src: &Path, dst: &Path) {
    copy_file(src, dst).unwrap_or_else(|_| {
        panic!("Unable to copy {:?} -> {:?}", src, dst);
    });
}

fn configure(build_dir: &Path, conf_line: &OsStr) {
    let mut conf = Command::new("sh");
    conf.current_dir(&build_dir).arg("-c").arg(conf_line);
    execute(conf);
}

fn make_and_check(env: &Environment, build_dir: &Path) {
    let mut make = Command::new("make");
    make.current_dir(build_dir).arg("-j").arg(&env.jobs);
    execute(make);
    if !env.c_no_tests && env.cross_target.is_none() {
        let mut make_check = Command::new("make");
        make_check
            .current_dir(build_dir)
            .arg("-j")
            .arg(&env.jobs)
            .arg("check");
        execute(make_check);
    }
}

#[cfg(unix)]
fn link_dir(src: &Path, dst: &Path) {
    println!("$ ln -s {:?} {:?}", src, dst);
    unix_fs::symlink(src, dst).unwrap_or_else(|_| {
        panic!("Unable to symlink {:?} -> {:?}", src, dst);
    });
}

#[cfg(windows)]
fn link_dir(src: &Path, dst: &Path) {
    println!("$ ln -s {:?} {:?}", src, dst);
    if windows_fs::symlink_dir(src, dst).is_ok() {
        return;
    }
    println!("symlink_dir: failed to create symbolic link, copying instead");
    let mut c = Command::new("cp");
    c.arg("-R").arg(src).arg(dst);
    execute(c);
}

fn mv(src: &str, dst_dir: &Path) {
    let mut c = Command::new("mv");
    c.arg(src).arg(".").current_dir(dst_dir);
    execute(c);
}

fn execute(mut command: Command) {
    println!("$ {:?}", command);
    let status = command
        .status()
        .unwrap_or_else(|_| panic!("Unable to execute: {:?}", command));
    if !status.success() {
        if let Some(code) = status.code() {
            panic!("Program failed with code {}: {:?}", code, command);
        } else {
            panic!("Program failed: {:?}", command);
        }
    }
}

fn execute_stdout(mut command: Command) -> Vec<u8> {
    println!("$ {:?}", command);
    let output = command
        .output()
        .unwrap_or_else(|_| panic!("Unable to execute: {:?}", command));
    if !output.status.success() {
        if let Some(code) = output.status.code() {
            panic!("Program failed with code {}: {:?}", code, command);
        } else {
            panic!("Program failed: {:?}", command);
        }
    }
    output.stdout
}

fn open(name: &Path) -> BufReader<File> {
    let file = File::open(name).unwrap_or_else(|_| panic!("Cannot open file: {:?}", name));
    BufReader::new(file)
}

fn create(name: &Path) -> BufWriter<File> {
    let file = File::create(name).unwrap_or_else(|_| panic!("Cannot create file: {:?}", name));
    BufWriter::new(file)
}

fn read_line(reader: &mut BufReader<File>, buf: &mut String, name: &Path) -> usize {
    reader
        .read_line(buf)
        .unwrap_or_else(|_| panic!("Cannot read from: {:?}", name))
}

fn write_flush(writer: &mut BufWriter<File>, buf: &str, name: &Path) {
    writer
        .write_all(buf.as_bytes())
        .unwrap_or_else(|_| panic!("Cannot write to: {:?}", name));
    writer
        .flush()
        .unwrap_or_else(|_| panic!("Cannot write to: {:?}", name));
}

fn system_cache_dir() -> Option<PathBuf> {
    #[cfg(target_os = "windows")]
    {
        use core::{mem::MaybeUninit, ptr, slice};
        use std::os::windows::ffi::OsStringExt;
        use winapi::{
            shared::winerror::S_OK,
            um::{combaseapi, knownfolders::FOLDERID_LocalAppData, shlobj, winbase},
        };
        let id = &FOLDERID_LocalAppData;
        let flags = 0;
        let access = ptr::null_mut();
        let mut path = MaybeUninit::uninit();
        unsafe {
            if shlobj::SHGetKnownFolderPath(id, flags, access, path.as_mut_ptr()) == S_OK {
                let path = path.assume_init();
                let slice = slice::from_raw_parts(path, winbase::lstrlenW(path) as usize);
                let string = OsString::from_wide(slice);
                combaseapi::CoTaskMemFree(path as _);
                Some(string.into())
            } else {
                None
            }
        }
    }
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    {
        env::var_os("HOME")
            .filter(|x| !x.is_empty())
            .map(|x| AsRef::<Path>::as_ref(&x).join("Library").join("Caches"))
    }
    #[cfg(not(any(target_os = "windows", target_os = "macos", target_os = "ios")))]
    {
        env::var_os("XDG_CACHE_HOME")
            .filter(|x| !x.is_empty())
            .map(PathBuf::from)
            .or_else(|| {
                env::var_os("HOME")
                    .filter(|x| !x.is_empty())
                    .map(|x| AsRef::<Path>::as_ref(&x).join(".cache"))
            })
    }
}

fn compilation_target_allowed(host: &str, target: &str) -> bool {
    if host == target {
        return true;
    }

    // Allow cross-compilation from x86_64 to i686, as it is a simple
    // -m32 switch in GMP compilation; unless MinGW is in use, where
    // cross compilation from 64-bit to 32-bit has issues.
    let (machine_x86_64, machine_i686) = ("x86_64", "i686");
    if host.starts_with(machine_x86_64)
        && target.starts_with(machine_i686)
        && host[machine_x86_64.len()..] == target[machine_i686.len()..]
        && !target.contains("-windows-gnu")
    {
        return true;
    }

    false
}

const BUG_47048_SAY_HI_C: &str = r#"/* say_hi.c */
#include <stdio.h>
void say_hi(void) {
    fprintf(stdout, "hi!\n");
}
"#;

const BUG_47048_C_MAIN_C: &str = r#"/* c_main.c */
void say_hi(void);
int main(void) {
    say_hi();
    return 0;
}
"#;

const BUG_47048_R_MAIN_RS: &str = r#"// r_main.rs
extern "C" {
    fn say_hi();
}
fn main() {
    unsafe {
        say_hi();
    }
}
"#;

const BUG_47048_WORKAROUND_C: &str = r#"/* workaround.c */
#define _CRTBLD
#include <stdio.h>

FILE *__cdecl __acrt_iob_func(unsigned index)
{
    return &(__iob_func()[index]);
}

typedef FILE *__cdecl (*_f__acrt_iob_func)(unsigned index);
_f__acrt_iob_func __MINGW_IMP_SYMBOL(__acrt_iob_func) = __acrt_iob_func;
"#;

// prints part of the header
const SYSTEM_GMP_C: &str = r##"/* system_gmp.c */
#include <gmp.h>
#include <stdio.h>

#define STRINGIFY(x) #x
#define DEFINE_STR(x) ("#define " #x " " STRINGIFY(x) "\n")

int main(void) {
    FILE *f = fopen("system_gmp.out", "w");

#ifdef _LONG_LONG_LIMB
    fputs(DEFINE_STR(_LONG_LONG_LIMB), f);
#else
    fputs("#undef _LONG_LONG_LIMB\n", f);
#endif

    fputs(DEFINE_STR(__GNU_MP_VERSION), f);
    fputs(DEFINE_STR(__GNU_MP_VERSION_MINOR), f);
    fputs(DEFINE_STR(__GNU_MP_VERSION_PATCHLEVEL), f);
    fputs(DEFINE_STR(GMP_LIMB_BITS), f);
    fputs(DEFINE_STR(GMP_NAIL_BITS), f);
    fputs(DEFINE_STR(__GMP_CC), f);
    fputs(DEFINE_STR(__GMP_CFLAGS), f);

    fclose(f);

    return 0;
}
"##;

// prints part of the header
const SYSTEM_MPFR_C: &str = r##"/* system_mpfr.c */
#include <mpfr.h>
#include <stdio.h>

#define STRINGIFY(x) #x
#define DEFINE_STR(x) ("#define " #x " " STRINGIFY(x) "\n")

int main(void) {
    FILE *f = fopen("system_mpfr.out", "w");

    fputs(DEFINE_STR(MPFR_VERSION_MAJOR), f);
    fputs(DEFINE_STR(MPFR_VERSION_MINOR), f);
    fputs(DEFINE_STR(MPFR_VERSION_PATCHLEVEL), f);
    fputs(DEFINE_STR(MPFR_VERSION_STRING), f);

    fclose(f);

    return 0;
}
"##;

// prints part of the header
const SYSTEM_MPC_C: &str = r##"/* system_mpc.c */
#include <mpc.h>
#include <stdio.h>

#define STRINGIFY(x) #x
#define DEFINE_STR(x) ("#define " #x " " STRINGIFY(x) "\n")

int main(void) {
    FILE *f = fopen("system_mpc.out", "w");

    fputs(DEFINE_STR(MPC_VERSION_MAJOR), f);
    fputs(DEFINE_STR(MPC_VERSION_MINOR), f);
    fputs(DEFINE_STR(MPC_VERSION_PATCHLEVEL), f);
    fputs(DEFINE_STR(MPC_VERSION_STRING), f);

    fclose(f);

    return 0;
}
"##;

const TRY_EXTENDED_KEY_VALUE_ATTRIBUTES: &str = r#"// try_extended_key_value_attributes.rs
#[doc = include_str!("try_extended_key_value_attributes.rs")]
pub struct S;
fn main() {}
"#;

const TRY_UNSAFE_IN_UNSAFE: &str = r#"// try_unsafe_in_unsafe.rs
#![deny(unknown_lints)]
#![warn(unsafe_op_in_unsafe_fn)]
fn main() {}
"#;
