// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include "fugue.h"
#include "crypto/sph_fugue.h"

inline void fugue_hash(const char* input, char* output, uint32_t len)
{   
    sph_fugue256_context ctx_fugue;
    sph_fugue256_init(&ctx_fugue);
    sph_fugue256(&ctx_fugue, input, len);
    sph_fugue256_close(&ctx_fugue, output);
}
