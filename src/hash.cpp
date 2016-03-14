// Copyright (c) 2013-2014 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "hash.h"
#include "crypto/common.h"
#include "crypto/hmac_sha512.h"
#include "pubkey.h"
#include "sync.h"
#include "utilstrencodings.h"
#include "util.h"


static void * V0 = NULL;


uint256 HashModifiedScrypt(const CBlockHeader *obj, void *_V0)
{
    uint256 returnBuffer;
    
    // If provided a V0 memory buffer the hash can be processed concurrently with others, this is done by miner threads
    if( _V0 != NULL ) {
        crypto_1M_1_1_256_scrypt( (uint8_t *)(BEGIN(obj->nVersion)), 80, _V0, (uint8_t *)(BEGIN(returnBuffer)), 32 );
        return returnBuffer;
    }
    
    // No memory buffer provided, create a common shared memory buffer and serialize access
    // This version is used by general non-miner threads which usually call GetHash serially already
    
    static CCriticalSection csHashModifiedScrypt;    // Only one block hash at a time due to avoid out-of-memory on lighter nodes
    LOCK( csHashModifiedScrypt );
    
    if( V0 == NULL ) {
        LogPrintf("HashModifiedScrypt(): Allocating large memory region\n");
        // Allocate buffer for scrypt to run if first run and not allocated
        // Large memory requirement only allows for a single block hash to be performed at a time
        V0 = malloc(128 * 1024 * 1024 + 63);
        LogPrintf("HashModifiedScrypt(): Allocated 128MB at %p\n", V0);
	
	if( V0 == NULL ) {
            LogPrintf("Error in HashModifiedScrypt: Out of memory, cannot not allocate 128MB for modified scrypte hashing\n");
	    throw std::runtime_error("HashModifiedScrypt(): Out of memory");
	}
    }
    
    crypto_1M_1_1_256_scrypt( (uint8_t *)(BEGIN(obj->nVersion)), 80, V0, (uint8_t *)(BEGIN(returnBuffer)), 32 );
    
    return returnBuffer;
}


inline uint32_t ROTL32(uint32_t x, int8_t r)
{
    return (x << r) | (x >> (32 - r));
}

unsigned int MurmurHash3(unsigned int nHashSeed, const std::vector<unsigned char>& vDataToHash)
{
    // The following is MurmurHash3 (x86_32), see http://code.google.com/p/smhasher/source/browse/trunk/MurmurHash3.cpp
    uint32_t h1 = nHashSeed;
    if (vDataToHash.size() > 0)
    {
        const uint32_t c1 = 0xcc9e2d51;
        const uint32_t c2 = 0x1b873593;

        const int nblocks = vDataToHash.size() / 4;

        //----------
        // body
        const uint8_t* blocks = &vDataToHash[0] + nblocks * 4;

        for (int i = -nblocks; i; i++) {
            uint32_t k1 = ReadLE32(blocks + i*4);

            k1 *= c1;
            k1 = ROTL32(k1, 15);
            k1 *= c2;

            h1 ^= k1;
            h1 = ROTL32(h1, 13);
            h1 = h1 * 5 + 0xe6546b64;
        }

        //----------
        // tail
        const uint8_t* tail = (const uint8_t*)(&vDataToHash[0] + nblocks * 4);

        uint32_t k1 = 0;

        switch (vDataToHash.size() & 3) {
        case 3:
            k1 ^= tail[2] << 16;
        case 2:
            k1 ^= tail[1] << 8;
        case 1:
            k1 ^= tail[0];
            k1 *= c1;
            k1 = ROTL32(k1, 15);
            k1 *= c2;
            h1 ^= k1;
        };
    }

    //----------
    // finalization
    h1 ^= vDataToHash.size();
    h1 ^= h1 >> 16;
    h1 *= 0x85ebca6b;
    h1 ^= h1 >> 13;
    h1 *= 0xc2b2ae35;
    h1 ^= h1 >> 16;

    return h1;
}

void BIP32Hash(const ChainCode &chainCode, unsigned int nChild, unsigned char header, const unsigned char data[32], unsigned char output[64])
{
    unsigned char num[4];
    num[0] = (nChild >> 24) & 0xFF;
    num[1] = (nChild >> 16) & 0xFF;
    num[2] = (nChild >>  8) & 0xFF;
    num[3] = (nChild >>  0) & 0xFF;
    CHMAC_SHA512(chainCode.begin(), chainCode.size()).Write(&header, 1).Write(data, 32).Write(num, 4).Finalize(output);
}
