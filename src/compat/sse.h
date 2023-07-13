// Copyright (c) 2019-2022 The Centure developers
// Authored by: Malcolm MacLeod (mmacleod@gmx.com)
// Distributed under the GNU Lesser General Public License v3, see the accompanying
// file COPYING

// This file defines a basic compatibility layer to compile sse instructions to neon on arm achitectures.
// The result is not likely to be optimal or as good as a complete neon re-write but still better than a naive non-neon implementation.

#ifndef COMPAT_SSE_H
#define COMPAT_SSE_H

#include <compat/arch.h>
#include <cstdint>

#if defined(ARCH_CPU_X86_FAMILY)
    #include <emmintrin.h>
    #include <immintrin.h>
    #ifndef USE_HARDWARE_AES
        // In the absence of AES-ni simply implement AES in software.
        #define SOFTWARE_AES
    #endif
#elif defined(ARCH_CPU_ARM_FAMILY)
    // Compat layer for neon intrinsics
    #if defined(USE_HARDWARE_AES) && !defined(__ARM_FEATURE_CRYPTO)
    #define __ARM_FEATURE_CRYPTO
    #endif   
    #include "sse2neon.h"
    // We currently use the following sse2neon commands:
    // _mm_mul_epu32 _mm_sub_epi64 _mm_add_epi64 _mm_srli_epi64 _mm_slli_epi64 _mm_unpacklo_epi64 _mm_unpackhi_epi64 _mm_aesenc_si128
    // _mm_xor_si128 _mm_and_si128 _mm_add_epi32 _mm_loadu_si128 _mm_setzero_si128 _mm_storeu_si128 _mm_add_epi8 _mm_shuffle_epi8 _mm_set_epi32
    // _mm_srli_epi16 _mm_srli_si128 _mm_slli_si128 _mm_shuffle_epi32 
    #ifdef USE_HARDWARE_AES
        // Implements equivalent of 'aesenc' by combining AESE (with an empty key) and AESMC and then manually applying the real key as an xor operation
        // This unfortunately means an additional xor op; the compiler should be able to optimise this away for repeated calls however
        // See  https://blog.michaelbrase.com/2018/05/08/emulating-x86-aes-intrinsics-on-armv8-a for more details.
        inline __m128i _mm_aesenc_si128(__m128i a, __m128i b)
        {
            return vreinterpretq_s32_u8(vaesmcq_u8(vaeseq_u8(vreinterpretq_u8_s32(a), uint8x16_t{})) ^ vreinterpretq_u8_s32(b));
        }
    #else
        #ifdef ARCH_CPU_ARM64_FAMILY
            // In the absence of crypto extensions, implement aesenc using regular neon intrinsics instead.
            #define SOFTWARE_AES
            #define SOFTWARE_AES_NEON
        #else
            // As a last resort use a complete software implementation
            #define SOFTWARE_AES
        #endif
    #endif
#else
    //fixme: (SIGMA) riscv
    #include <array>
    typedef std::array<uint8_t, 16> __m128i;
#endif

#if defined(SOFTWARE_AES) || defined(SOFTWARE_AES_NEON)
    static const uint8_t crypto_aes_sbox[256] = { 0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76, 0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0, 0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15, 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75, 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84, 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf, 0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8, 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2, 0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73, 0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb, 0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79, 0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08, 0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a, 0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e, 0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf, 0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 };
    #ifdef SOFTWARE_AES_NEON
        // See: http://www.workofard.com/2017/01/accelerated-aes-for-the-arm64-linux-kernel/ http://www.workofard.com/2017/07/ghash-for-low-end-cores/ and https://github.com/ColinIanKing/linux-next-mirror/blob/b5f466091e130caaf0735976648f72bd5e09aa84/crypto/aegis128-neon-inner.c#L52 for more information
        // Reproduced with permission of the author.
        inline __m128i _mm_aesenc_si128_sw(__m128i EncBlock, __m128i RoundKey)
        {
            static const uint8_t crypto_aes_sbox[256] = { 0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76, 0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0, 0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15, 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75, 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84, 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf, 0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8, 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2, 0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73, 0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb, 0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79, 0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08, 0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a, 0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e, 0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf, 0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 };
            static const uint8_t shift_rows[] = { 0x0, 0x5, 0xa, 0xf, 0x4, 0x9, 0xe, 0x3, 0x8, 0xd, 0x2, 0x7, 0xc, 0x1, 0x6, 0xb};
            static const uint8_t ror32by8[] = {0x1, 0x2, 0x3, 0x0, 0x5, 0x6, 0x7, 0x4, 0x9, 0xa, 0xb, 0x8, 0xd, 0xe, 0xf, 0xc};

            uint8x16_t v;
            uint8x16_t w = vreinterpretq_u8_s32(EncBlock);

            // shift rows
            w = vqtbl1q_u8(w, vld1q_u8(shift_rows));

            // sub bytes
            v = vqtbl4q_u8(vld1q_u8_x4(crypto_aes_sbox), w);
            v = vqtbx4q_u8(v, vld1q_u8_x4(crypto_aes_sbox + 0x40), w - 0x40);
            v = vqtbx4q_u8(v, vld1q_u8_x4(crypto_aes_sbox + 0x80), w - 0x80);
            v = vqtbx4q_u8(v, vld1q_u8_x4(crypto_aes_sbox + 0xc0), w - 0xc0);

            // mix columns
            w = (v << 1) ^ (uint8x16_t)(((int8x16_t)v >> 7) & 0x1b);
            w ^= (uint8x16_t)vrev32q_u16((uint16x8_t)v);
            w ^= vqtbl1q_u8(v ^ w, vld1q_u8(ror32by8));

            //  add round key
            return vreinterpretq_s32_u8(w) ^ RoundKey;
        }
    #else
        #define XT(x) (((x) << 1) ^ ((((x) >> 7) & 1) * 0x1b))
        inline __m128i _mm_aesenc_si128_sw (__m128i a, __m128i b)
        {
            typedef union{__m128i u128; unsigned char u8[16];} u128_wrap;            
            uint8_t i, t, u, v[4][4];
            for (i = 0; i < 16; ++i)
            {
                v[((i / 4) + 4 - (i%4) ) % 4][i % 4] = crypto_aes_sbox[((u128_wrap*)&a)->u8[i]];
            }
            for (i = 0; i < 4; ++i)
            {
                t = v[i][0];
                u = v[i][0] ^ v[i][1] ^ v[i][2] ^ v[i][3];
                v[i][0] ^= u ^ XT(v[i][0] ^ v[i][1]);
                v[i][1] ^= u ^ XT(v[i][1] ^ v[i][2]);
                v[i][2] ^= u ^ XT( v[i][2] ^ v[i][3]);
                v[i][3] ^= u ^ XT(v[i][3] ^ t);
            }
            for (i = 0; i < 16; ++i)
            {
                ((u128_wrap*)&a)->u8[i] = v[i / 4][i % 4] ^ ((u128_wrap*)&b)->u8[i];
            }
            return ((u128_wrap*)&a)->u128;
        }
    #endif
#endif

#endif
