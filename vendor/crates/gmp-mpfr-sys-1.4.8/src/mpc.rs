// Copyright © 2017–2022 Trevor Spiteri

// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License and a copy of the GNU General Public License along with
// this program. If not, see <https://www.gnu.org/licenses/>.

/*!
Function and type bindings for the [MPC] library.

# Examples

```rust
use core::{f64, mem::MaybeUninit};
use gmp_mpfr_sys::{mpc, mpfr};
let one_third = 1.0_f64 / 3.0;
let neg_inf = f64::NEG_INFINITY;
unsafe {
    let mut c = MaybeUninit::uninit();
    mpc::init3(c.as_mut_ptr(), 53, 53);
    let mut c = c.assume_init();
    let dirs = mpc::set_d_d(&mut c, one_third, neg_inf, mpc::RNDNN);
    assert_eq!(dirs, 0);
    let re_ptr = mpc::realref_const(&c);
    let re = mpfr::get_d(re_ptr, mpfr::rnd_t::RNDN);
    assert_eq!(re, one_third);
    let im_ptr = mpc::imagref_const(&c);
    let im = mpfr::get_d(im_ptr, mpfr::rnd_t::RNDN);
    assert_eq!(im, neg_inf);
    mpc::clear(&mut c);
}
```

[MPC]: http://www.multiprecision.org/mpc/
*/
#![allow(non_camel_case_types, non_snake_case)]

use crate::{
    gmp::{mpf_t, mpq_t, mpz_t, randstate_t},
    mpfr::{mpfr_t, prec_t, rnd_t as mpfr_rnd_t},
};
use libc::{c_char, c_int, c_long, c_ulong, intmax_t, uintmax_t, FILE};

include!(concat!(env!("OUT_DIR"), "/mpc_h.rs"));

#[inline]
extern "C" fn INEX_NEG(inex: c_int) -> c_int {
    match inex {
        2 => -1,
        0 => 0,
        _ => 1,
    }
}
/// See: [Return Value](../C/MPC/constant.GNU_MPC_Basics.html#return_002dvalue)
#[inline]
pub extern "C" fn INEX_RE(inex: c_int) -> c_int {
    INEX_NEG((inex) & 3)
}
/// See: [Return Value](../C/MPC/constant.GNU_MPC_Basics.html#return_002dvalue)
#[inline]
pub extern "C" fn INEX_IM(inex: c_int) -> c_int {
    INEX_NEG((inex) >> 2)
}
/// See: [Return Value](../C/MPC/constant.GNU_MPC_Basics.html#return_002dvalue)
#[inline]
pub extern "C" fn INEX1(inex: c_int) -> c_int {
    inex & 15
}
/// See: [Return Value](../C/MPC/constant.GNU_MPC_Basics.html#return_002dvalue)
#[inline]
pub extern "C" fn INEX2(inex: c_int) -> c_int {
    inex >> 4
}

/// See: [`mpc_rnd_t`](../C/MPC/constant.GNU_MPC_Basics.html#index-mpc_005frnd_005ft)
pub type rnd_t = c_int;

const RNDN: c_int = mpfr_rnd_t::RNDN as c_int;
const RNDZ: c_int = mpfr_rnd_t::RNDZ as c_int;
const RNDU: c_int = mpfr_rnd_t::RNDU as c_int;
const RNDD: c_int = mpfr_rnd_t::RNDD as c_int;

/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDNN: c_int = RNDN + (RNDN << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDNZ: c_int = RNDN + (RNDZ << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDNU: c_int = RNDN + (RNDU << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDND: c_int = RNDN + (RNDD << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDZN: c_int = RNDZ + (RNDN << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDZZ: c_int = RNDZ + (RNDZ << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDZU: c_int = RNDZ + (RNDU << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDZD: c_int = RNDZ + (RNDD << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDUN: c_int = RNDU + (RNDN << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDUZ: c_int = RNDU + (RNDZ << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDUU: c_int = RNDU + (RNDU << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDUD: c_int = RNDU + (RNDD << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDDN: c_int = RNDD + (RNDN << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDDZ: c_int = RNDD + (RNDZ << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDDU: c_int = RNDD + (RNDU << 4);
/// See: [Rounding Modes](../C/MPC/constant.GNU_MPC_Basics.html#Rounding-Modes)
pub const RNDDD: c_int = RNDD + (RNDD << 4);

/// See: [`mpc_t`](../C/MPC/constant.GNU_MPC_Basics.html#index-mpc_005ft)
///
/// # Future compatibility
///
/// The fields listed here are considered internal details. These
/// internals may change in new minor releases of this crate, though
/// they will be kept unchanged for patch releases. Any code that
/// makes use of these internals should list the dependency as
/// `version = "~1.4"` inside [*Cargo.toml*], *not* `version = "1.4"`.
///
/// [*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct mpc_t {
    /// Internal implementation detail: real part.
    pub re: mpfr_t,
    /// Internal implementation detail: imaginary part.
    pub im: mpfr_t,
}

// Types for function declarations in this file.

type mpz_srcptr = *const mpz_t;
type mpq_srcptr = *const mpq_t;
type mpf_srcptr = *const mpf_t;
type randstate_ptr = *mut randstate_t;
type mpfr_srcptr = *const mpfr_t;
type mpfr_ptr = *mut mpfr_t;
type mpc_ptr = *mut mpc_t;
type mpc_srcptr = *const mpc_t;

extern "C" {
    // Initialization Functions

    /// See: [`mpc_init2`](../C/MPC/constant.Complex_Functions.html#index-mpc_005finit2)
    #[link_name = "mpc_init2"]
    pub fn init2(z: mpc_ptr, prec: prec_t);
    /// See: [`mpc_init3`](../C/MPC/constant.Complex_Functions.html#index-mpc_005finit3)
    #[link_name = "mpc_init3"]
    pub fn init3(z: mpc_ptr, prec_r: prec_t, prec_i: prec_t);
    /// See: [`mpc_clear`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fclear)
    #[link_name = "mpc_clear"]
    pub fn clear(z: mpc_ptr);
    /// See: [`mpc_set_prec`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fprec)
    #[link_name = "mpc_set_prec"]
    pub fn set_prec(x: mpc_ptr, prec: prec_t);
    /// See: [`mpc_get_prec`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fget_005fprec)
    #[link_name = "mpc_get_prec"]
    pub fn get_prec(x: mpc_srcptr) -> prec_t;
    /// See: [`mpc_get_prec2`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fget_005fprec2)
    #[link_name = "mpc_get_prec2"]
    pub fn get_prec2(pr: *mut prec_t, pi: *mut prec_t, x: mpc_srcptr);

    // Assignment Functions

    /// See: [`mpc_set`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset)
    #[link_name = "mpc_set"]
    pub fn set(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_ui`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fui)
    #[link_name = "mpc_set_ui"]
    pub fn set_ui(rop: mpc_ptr, op: c_ulong, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_si`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fsi)
    #[link_name = "mpc_set_si"]
    pub fn set_si(rop: mpc_ptr, op: c_long, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_uj`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fuj)
    #[link_name = "mpc_set_uj"]
    pub fn set_uj(rop: mpc_ptr, op: uintmax_t, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_sj`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fsj)
    #[link_name = "mpc_set_sj"]
    pub fn set_sj(rop: mpc_ptr, op: intmax_t, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_d`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fd)
    #[link_name = "mpc_set_d"]
    pub fn set_d(rop: mpc_ptr, op: f64, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_z`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fz)
    #[link_name = "mpc_set_z"]
    pub fn set_z(rop: mpc_ptr, op: mpz_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_q`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fq)
    #[link_name = "mpc_set_q"]
    pub fn set_q(rop: mpc_ptr, op: mpq_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_f`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005ff)
    #[link_name = "mpc_set_f"]
    pub fn set_f(rop: mpc_ptr, op: mpf_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_fr`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005ffr)
    #[link_name = "mpc_set_fr"]
    pub fn set_fr(rop: mpc_ptr, op: mpfr_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_ui_ui`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fui_005fui)
    #[link_name = "mpc_set_ui_ui"]
    pub fn set_ui_ui(rop: mpc_ptr, op1: c_ulong, op2: c_ulong, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_si_si`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fsi_005fsi)
    #[link_name = "mpc_set_si_si"]
    pub fn set_si_si(rop: mpc_ptr, op1: c_long, op2: c_long, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_uj_uj`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fuj_005fuj)
    #[link_name = "mpc_set_uj_uj"]
    pub fn set_uj_uj(rop: mpc_ptr, op1: uintmax_t, op2: uintmax_t, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_sj_sj`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fsj_005fsj)
    #[link_name = "mpc_set_sj_sj"]
    pub fn set_sj_sj(rop: mpc_ptr, op1: intmax_t, op2: intmax_t, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_d_d`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fd_005fd)
    #[link_name = "mpc_set_d_d"]
    pub fn set_d_d(rop: mpc_ptr, op1: f64, op2: f64, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_z_z`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fz_005fz)
    #[link_name = "mpc_set_z_z"]
    pub fn set_z_z(rop: mpc_ptr, op1: mpz_srcptr, op2: mpz_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_q_q`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fq_005fq)
    #[link_name = "mpc_set_q_q"]
    pub fn set_q_q(rop: mpc_ptr, op1: mpq_srcptr, op2: mpq_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_f_f`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005ff_005ff)
    #[link_name = "mpc_set_f_f"]
    pub fn set_f_f(rop: mpc_ptr, op1: mpf_srcptr, op2: mpf_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_fr_fr`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005ffr_005ffr)
    #[link_name = "mpc_set_fr_fr"]
    pub fn set_fr_fr(rop: mpc_ptr, op1: mpfr_srcptr, op2: mpfr_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_set_nan`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fnan)
    #[link_name = "mpc_set_nan"]
    pub fn set_nan(rop: mpc_ptr);
    /// See: [`mpc_swap`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fswap)
    #[link_name = "mpc_swap"]
    pub fn swap(op1: mpc_ptr, op2: mpc_ptr);

    // String and Stream Input and Output

    /// See: [`mpc_strtoc`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fstrtoc)
    #[link_name = "mpc_strtoc"]
    pub fn strtoc(
        rop: mpc_ptr,
        nptr: *const c_char,
        endptr: *mut *mut c_char,
        base: c_int,
        rnd: rnd_t,
    ) -> c_int;
    /// See: [`mpc_set_str`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fset_005fstr)
    #[link_name = "mpc_set_str"]
    pub fn set_str(rop: mpc_ptr, s: *const c_char, base: c_int, rnd: rnd_t) -> c_int;
    /// See: [`mpc_get_str`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fget_005fstr)
    #[link_name = "mpc_get_str"]
    pub fn get_str(b: c_int, n: usize, op: mpc_srcptr, rnd: rnd_t) -> *mut c_char;
    /// See: [`mpc_free_str`](../C/MPC/constant.Complex_Functions.html#index-mpc_005ffree_005fstr)
    #[link_name = "mpc_free_str"]
    pub fn free_str(rop: *mut c_char);
    /// See: [`mpc_inp_str`](../C/MPC/constant.Complex_Functions.html#index-mpc_005finp_005fstr)
    #[link_name = "mpc_inp_str"]
    pub fn inp_str(
        rop: mpc_ptr,
        stream: *mut FILE,
        read: *mut usize,
        base: c_int,
        rnd: rnd_t,
    ) -> c_int;
    /// See: [`mpc_out_str`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fout_005fstr)
    #[link_name = "mpc_out_str"]
    pub fn out_str(
        stream: *mut FILE,
        base: c_int,
        n_digits: usize,
        op: mpc_srcptr,
        rnd: rnd_t,
    ) -> usize;

    // Comparison Functions

    /// See: [`mpc_cmp`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fcmp)
    #[link_name = "mpc_cmp"]
    pub fn cmp(op1: mpc_srcptr, op2: mpc_srcptr) -> c_int;
    /// See: [`mpc_cmp_si_si`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fcmp_005fsi_005fsi)
    #[link_name = "mpc_cmp_si_si"]
    pub fn cmp_si_si(op1: mpc_srcptr, op2r: c_long, op2i: c_long) -> c_int;
}
/// See: [`mpc_cmp_si`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fcmp_005fsi)
#[inline]
pub unsafe extern "C" fn cmp_si(op1: mpc_srcptr, op2: c_long) -> c_int {
    unsafe { cmp_si_si(op1, op2, 0) }
}
extern "C" {
    /// See: [`mpc_cmp_abs`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fcmp_005fabs)
    #[link_name = "mpc_cmp_abs"]
    pub fn cmp_abs(op1: mpc_srcptr, op2: mpc_srcptr) -> c_int;

    // Projection and Decomposing Functions
    /// See: [`mpc_real`](../C/MPC/constant.Complex_Functions.html#index-mpc_005freal)
    #[link_name = "mpc_real"]
    pub fn real(rop: mpfr_ptr, arg2: mpc_srcptr, rnd: mpfr_rnd_t) -> c_int;
    /// See: [`mpc_imag`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fimag)
    #[link_name = "mpc_imag"]
    pub fn imag(rop: mpfr_ptr, arg2: mpc_srcptr, rnd: mpfr_rnd_t) -> c_int;
}
/// See: [`mpc_realref`](../C/MPC/constant.Complex_Functions.html#index-mpc_005frealref)
#[inline]
pub unsafe extern "C" fn realref(op: mpc_ptr) -> mpfr_ptr {
    op as mpfr_ptr
}
/// Constant version of [`realref`](fn.realref.html).
#[inline]
pub unsafe extern "C" fn realref_const(op: mpc_srcptr) -> mpfr_srcptr {
    op as mpfr_srcptr
}
/// See: [`mpc_imagref`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fimagref)
#[inline]
pub unsafe extern "C" fn imagref(op: mpc_ptr) -> mpfr_ptr {
    unsafe { (op as mpfr_ptr).offset(1) }
}
/// Constant version of [`imagref`](fn.imagref.html).
#[inline]
pub unsafe extern "C" fn imagref_const(op: mpc_srcptr) -> mpfr_srcptr {
    unsafe { (op as mpfr_srcptr).offset(1) }
}
extern "C" {
    /// See: [`mpc_arg`](../C/MPC/constant.Complex_Functions.html#index-mpc_005farg)
    #[link_name = "mpc_arg"]
    pub fn arg(rop: mpfr_ptr, op: mpc_srcptr, rnd: mpfr_rnd_t) -> c_int;
    /// See: [`mpc_proj`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fproj)
    #[link_name = "mpc_proj"]
    pub fn proj(rop: mpc_ptr, arg2: mpc_srcptr, rnd: rnd_t) -> c_int;

    // Basic Arithmetic Functions

    /// See: [`mpc_add`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fadd)
    #[link_name = "mpc_add"]
    pub fn add(rop: mpc_ptr, op1: mpc_srcptr, op2: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_add_ui`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fadd_005fui)
    #[link_name = "mpc_add_ui"]
    pub fn add_ui(rop: mpc_ptr, op1: mpc_srcptr, op2: c_ulong, rnd: rnd_t) -> c_int;
    /// See: [`mpc_add_fr`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fadd_005ffr)
    #[link_name = "mpc_add_fr"]
    pub fn add_fr(rop: mpc_ptr, op1: mpc_srcptr, op2: mpfr_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_fr_sub`](../C/MPC/constant.Complex_Functions.html#index-mpc_005ffr_005fsub)
    #[link_name = "mpc_sub"]
    pub fn sub(rop: mpc_ptr, op1: mpc_srcptr, op2: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_sub_fr`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fsub_005ffr)
    #[link_name = "mpc_sub_fr"]
    pub fn sub_fr(rop: mpc_ptr, op1: mpc_srcptr, op2: mpfr_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_fr_sub`](../C/MPC/constant.Complex_Functions.html#index-mpc_005ffr_005fsub)
    #[link_name = "mpc_fr_sub"]
    pub fn fr_sub(rop: mpc_ptr, op1: mpfr_srcptr, op2: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_sub_ui`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fsub_005fui)
    #[link_name = "mpc_sub_ui"]
    pub fn sub_ui(rop: mpc_ptr, op1: mpc_srcptr, op2: c_ulong, rnd: rnd_t) -> c_int;
}
/// See: [`mpc_ui_sub`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fui_005fsub)
#[inline]
pub unsafe extern "C" fn ui_sub(rop: mpc_ptr, op1: c_ulong, op2: mpc_srcptr, rnd: rnd_t) -> c_int {
    unsafe { ui_ui_sub(rop, op1, 0, op2, rnd) }
}
extern "C" {
    /// See: [`mpc_ui_ui_sub`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fui_005fui_005fsub)
    #[link_name = "mpc_ui_ui_sub"]
    pub fn ui_ui_sub(
        rop: mpc_ptr,
        re1: c_ulong,
        im1: c_ulong,
        op2: mpc_srcptr,
        rnd: rnd_t,
    ) -> c_int;
    /// See: [`mpc_neg`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fneg)
    #[link_name = "mpc_neg"]
    pub fn neg(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_sum`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fsum)
    #[link_name = "mpc_sum"]
    pub fn sum(rop: mpc_ptr, op: *const mpc_ptr, n: c_ulong, rnd: rnd_t) -> c_int;
    /// See: [`mpc_mul`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fmul)
    #[link_name = "mpc_mul"]
    pub fn mul(rop: mpc_ptr, op1: mpc_srcptr, op2: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_mul_ui`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fmul_005fui)
    #[link_name = "mpc_mul_ui"]
    pub fn mul_ui(rop: mpc_ptr, op1: mpc_srcptr, op2: c_ulong, rnd: rnd_t) -> c_int;
    /// See: [`mpc_mul_si`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fmul_005fsi)
    #[link_name = "mpc_mul_si"]
    pub fn mul_si(rop: mpc_ptr, op1: mpc_srcptr, op2: c_long, rnd: rnd_t) -> c_int;
    /// See: [`mpc_mul_fr`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fmul_005ffr)
    #[link_name = "mpc_mul_fr"]
    pub fn mul_fr(rop: mpc_ptr, op1: mpc_srcptr, op2: mpfr_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_mul_i`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fmul_005fi)
    #[link_name = "mpc_mul_i"]
    pub fn mul_i(rop: mpc_ptr, op: mpc_srcptr, sgn: c_int, rnd: rnd_t) -> c_int;
    /// See: [`mpc_sqr`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fsqr)
    #[link_name = "mpc_sqr"]
    pub fn sqr(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_fma`](../C/MPC/constant.Complex_Functions.html#index-mpc_005ffma)
    #[link_name = "mpc_fma"]
    pub fn fma(
        rop: mpc_ptr,
        op1: mpc_srcptr,
        op2: mpc_srcptr,
        op3: mpc_srcptr,
        rnd: rnd_t,
    ) -> c_int;
    /// See: [`mpc_dot`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fdot)
    #[link_name = "mpc_dot"]
    pub fn dot(
        rop: mpc_ptr,
        op1: *const mpc_ptr,
        op2: *const mpc_ptr,
        n: c_ulong,
        rnd: rnd_t,
    ) -> c_int;
    /// See: [`mpc_div`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fdiv)
    #[link_name = "mpc_div"]
    pub fn div(rop: mpc_ptr, op1: mpc_srcptr, op2: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_div_ui`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fdiv_005fui)
    #[link_name = "mpc_div_ui"]
    pub fn div_ui(rop: mpc_ptr, op1: mpc_srcptr, op2: c_ulong, rnd: rnd_t) -> c_int;
    /// See: [`mpc_div_fr`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fdiv_005ffr)
    #[link_name = "mpc_div_fr"]
    pub fn div_fr(rop: mpc_ptr, op1: mpc_srcptr, op2: mpfr_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_ui_div`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fui_005fdiv)
    #[link_name = "mpc_ui_div"]
    pub fn ui_div(rop: mpc_ptr, op1: c_ulong, op2: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_fr_div`](../C/MPC/constant.Complex_Functions.html#index-mpc_005ffr_005fdiv)
    #[link_name = "mpc_fr_div"]
    pub fn fr_div(rop: mpc_ptr, op1: mpfr_srcptr, op2: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_conj`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fconj)
    #[link_name = "mpc_conj"]
    pub fn conj(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_abs`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fabs)
    #[link_name = "mpc_abs"]
    pub fn abs(rop: mpfr_ptr, op: mpc_srcptr, rnd: mpfr_rnd_t) -> c_int;
    /// See: [`mpc_norm`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fnorm)
    #[link_name = "mpc_norm"]
    pub fn norm(rop: mpfr_ptr, op: mpc_srcptr, rnd: mpfr_rnd_t) -> c_int;
    /// See: [`mpc_mul_2ui`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fmul_005f2ui)
    #[link_name = "mpc_mul_2ui"]
    pub fn mul_2ui(rop: mpc_ptr, op1: mpc_srcptr, op2: c_ulong, rnd: rnd_t) -> c_int;
    /// See: [`mpc_mul_2si`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fmul_005f2si)
    #[link_name = "mpc_mul_2si"]
    pub fn mul_2si(rop: mpc_ptr, op1: mpc_srcptr, op2: c_long, rnd: rnd_t) -> c_int;
    /// See: [`mpc_div_2ui`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fdiv_005f2ui)
    #[link_name = "mpc_div_2ui"]
    pub fn div_2ui(rop: mpc_ptr, op1: mpc_srcptr, op2: c_ulong, rnd: rnd_t) -> c_int;
    /// See: [`mpc_div_2si`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fdiv_005f2si)
    #[link_name = "mpc_div_2si"]
    pub fn div_2si(rop: mpc_ptr, op1: mpc_srcptr, op2: c_long, rnd: rnd_t) -> c_int;

    // Power Functions and Logarithms

    /// See: [`mpc_sqrt`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fsqrt)
    #[link_name = "mpc_sqrt"]
    pub fn sqrt(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_pow`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fpow)
    #[link_name = "mpc_pow"]
    pub fn pow(rop: mpc_ptr, op1: mpc_srcptr, op2: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_pow_d`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fpow_005fd)
    #[link_name = "mpc_pow_d"]
    pub fn pow_d(rop: mpc_ptr, op1: mpc_srcptr, op2: f64, rnd: rnd_t) -> c_int;
    /// See: [`mpc_pow_si`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fpow_005fsi)
    #[link_name = "mpc_pow_si"]
    pub fn pow_si(rop: mpc_ptr, op1: mpc_srcptr, op2: c_long, rnd: rnd_t) -> c_int;
    /// See: [`mpc_pow_ui`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fpow_005fui)
    #[link_name = "mpc_pow_ui"]
    pub fn pow_ui(rop: mpc_ptr, op1: mpc_srcptr, op2: c_ulong, rnd: rnd_t) -> c_int;
    /// See: [`mpc_pow_z`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fpow_005fz)
    #[link_name = "mpc_pow_z"]
    pub fn pow_z(rop: mpc_ptr, op1: mpc_srcptr, op2: mpz_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_pow_fr`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fpow_005ffr)
    #[link_name = "mpc_pow_fr"]
    pub fn pow_fr(rop: mpc_ptr, op1: mpc_srcptr, op2: mpfr_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_exp`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fexp)
    #[link_name = "mpc_exp"]
    pub fn exp(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_log`](../C/MPC/constant.Complex_Functions.html#index-mpc_005flog)
    #[link_name = "mpc_log"]
    pub fn log(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_log10`](../C/MPC/constant.Complex_Functions.html#index-mpc_005flog10)
    #[link_name = "mpc_log10"]
    pub fn log10(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_rootofunity`](../C/MPC/constant.Complex_Functions.html#index-mpc_005frootofunity)
    #[link_name = "mpc_rootofunity"]
    pub fn rootofunity(rop: mpc_ptr, n: c_ulong, k: c_ulong, rnd: rnd_t) -> c_int;

    // Trigonometric Functions

    /// See: [`mpc_sin`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fsin)
    #[link_name = "mpc_sin"]
    pub fn sin(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_cos`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fcos)
    #[link_name = "mpc_cos"]
    pub fn cos(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_sin_cos`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fsin_005fcos)
    #[link_name = "mpc_sin_cos"]
    pub fn sin_cos(
        rop_sin: mpc_ptr,
        rop_cos: mpc_ptr,
        op: mpc_srcptr,
        rnd_sin: rnd_t,
        rnd_cos: rnd_t,
    ) -> c_int;
    /// See: [`mpc_tan`](../C/MPC/constant.Complex_Functions.html#index-mpc_005ftan)
    #[link_name = "mpc_tan"]
    pub fn tan(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_sinh`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fsinh)
    #[link_name = "mpc_sinh"]
    pub fn sinh(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_cosh`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fcosh)
    #[link_name = "mpc_cosh"]
    pub fn cosh(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_tanh`](../C/MPC/constant.Complex_Functions.html#index-mpc_005ftanh)
    #[link_name = "mpc_tanh"]
    pub fn tanh(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_asin`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fasin)
    #[link_name = "mpc_asin"]
    pub fn asin(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_acos`](../C/MPC/constant.Complex_Functions.html#index-mpc_005facos)
    #[link_name = "mpc_acos"]
    pub fn acos(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_atan`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fatan)
    #[link_name = "mpc_atan"]
    pub fn atan(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_asinh`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fasinh)
    #[link_name = "mpc_asinh"]
    pub fn asinh(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_acosh`](../C/MPC/constant.Complex_Functions.html#index-mpc_005facosh)
    #[link_name = "mpc_acosh"]
    pub fn acosh(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;
    /// See: [`mpc_atanh`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fatanh)
    #[link_name = "mpc_atanh"]
    pub fn atanh(rop: mpc_ptr, op: mpc_srcptr, rnd: rnd_t) -> c_int;

    // Miscellaneous Functions

    /// See: [`mpc_urandom`](../C/MPC/constant.Complex_Functions.html#index-mpc_005furandom)
    #[link_name = "mpc_urandom"]
    pub fn urandom(rop: mpc_ptr, state: randstate_ptr) -> c_int;
    /// See: [`mpc_get_version`](../C/MPC/constant.Complex_Functions.html#index-mpc_005fget_005fversion)
    #[link_name = "mpc_get_version"]
    pub fn get_version() -> *const c_char;
}
/// See: [`MPC_VERSION`](../C/MPC/constant.Complex_Functions.html#index-MPC_005fVERSION)
pub const VERSION: c_int = (VERSION_MAJOR << 16) | (VERSION_MINOR << 8) | VERSION_PATCHLEVEL;
/// See: [`MPC_VERSION_MAJOR`](../C/MPC/constant.Complex_Functions.html#index-MPC_005fVERSION_005fMAJOR)
pub const VERSION_MAJOR: c_int = MPC_VERSION_MAJOR;
/// See: [`MPC_VERSION_MINOR`](../C/MPC/constant.Complex_Functions.html#index-MPC_005fVERSION_005fMINOR)
pub const VERSION_MINOR: c_int = MPC_VERSION_MINOR;
/// See: [`MPC_VERSION_PATCHLEVEL`](../C/MPC/constant.Complex_Functions.html#index-MPC_005fVERSION_005fPATCHLEVEL)
pub const VERSION_PATCHLEVEL: c_int = MPC_VERSION_PATCHLEVEL;
/// See: [`MPC_VERSION_STRING`](../C/MPC/constant.Complex_Functions.html#index-MPC_005fVERSION_005fSTRING)
pub const VERSION_STRING: *const c_char = MPC_VERSION_STRING;
/// See: [`MPC_VERSION_NUM`](../C/MPC/constant.Complex_Functions.html#index-MPC_005fVERSION_005fNUM)
#[inline]
pub extern "C" fn VERSION_NUM(major: c_int, minor: c_int, patchlevel: c_int) -> c_int {
    (major << 16) | (minor << 8) | patchlevel
}

#[cfg(test)]
mod tests {
    use crate::{gmp, mpc, mpfr};
    use core::ptr::NonNull;

    #[test]
    fn check_real_imag_offsets() {
        let mut limbs: [gmp::limb_t; 2] = [1 << (gmp::LIMB_BITS - 1), 1 << (gmp::LIMB_BITS - 1)];
        let mut c = mpc::mpc_t {
            re: mpfr::mpfr_t {
                prec: 1,
                sign: 1,
                exp: 0,
                d: NonNull::from(&mut limbs[0]),
            },
            im: mpfr::mpfr_t {
                prec: 1,
                sign: 1,
                exp: 0,
                d: NonNull::from(&mut limbs[1]),
            },
        };
        unsafe {
            assert_eq!(&c.re as *const mpfr::mpfr_t, mpc::realref_const(&c));
            assert_eq!(&c.im as *const mpfr::mpfr_t, mpc::imagref_const(&c));
            assert_eq!(&mut c.re as *mut mpfr::mpfr_t, mpc::realref(&mut c));
            assert_eq!(&mut c.im as *mut mpfr::mpfr_t, mpc::imagref(&mut c));
        }
    }

    #[test]
    fn check_version() {
        use crate::tests;

        let (major, minor, patchlevel) = (1, 2, 1);
        let version = "1.2.1";

        assert_eq!(mpc::VERSION_MAJOR, major);
        assert!(mpc::VERSION_MINOR >= minor);
        if cfg!(not(feature = "use-system-libs")) {
            assert!(mpc::VERSION_MINOR > minor || mpc::VERSION_PATCHLEVEL >= patchlevel);
            if mpc::VERSION_MINOR == minor && mpc::VERSION_PATCHLEVEL == patchlevel {
                assert_eq!(unsafe { tests::str_from_cstr(mpc::get_version()) }, version);
                assert_eq!(
                    unsafe { tests::str_from_cstr(mpc::VERSION_STRING) },
                    version
                );
            }
        }
    }
}
