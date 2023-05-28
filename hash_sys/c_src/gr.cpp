// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

#include "gr.h"
#include "hash.h"
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include "uint256.h"

void gr_hash(const char* input, const char* key, char* output) {
    std::vector<unsigned char> outputkey(32);
    std::transform(key, key+32, outputkey.begin(),
        [](char c)
        {
        return static_cast<unsigned char>(c);
        });
    uint256 res = HashGR(input, input + 32, *new uint256(outputkey));
    for (int i = 0; i < 32; i++) {
        output[i] = res.data[i];
    }
}