// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>

extern "C" {
    void gr_hash(const char* input, const char* key, char* output);
}