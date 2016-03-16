// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "primitives/block.h"

#include "hash.h"
#include "tinyformat.h"
#include "utilstrencodings.h"
#include "crypto/common.h"
#include "util.h"

#include <boost/filesystem/path.hpp>
#include <boost/filesystem.hpp>
#include "streams.h"
#include <stdint.h>
#include "clientversion.h"
#include "sync.h"


static std::map<CBlockHeaderHashKey,uint256> hashCache;    // A cache of past modified scrypt hashes performed
static CCriticalSection                      csHashCache;
static CCriticalSection                      csAddToDisk;


uint256 CBlockHeader::GetHash(bool useCache, void * V0) const
{
    uint256             returnHash;

    CBlockHeaderHashKey key(*this);
  
    // Use SHA256 if block version indicates legacy PoW
    if (nVersion < FULL_FORK_VERSION || nVersion > FULL_FORK_VERSION_MAX) {
        return SerializeHash(*this);
    }
    
    // Use modified scrypt for PoW for versions equal or above the fork version (ignoring alternative fork versions for now)
    //
    // Due to the long hash runtime and the fact bitcoind requests the same hash multiple times during a block 
    //   validation, cache previous hashes and return the cached result if available
    if( useCache ) {
        LOCK(csHashCache);
        std::map<CBlockHeaderHashKey,uint256>::iterator search = hashCache.find(key);
        if(search != hashCache.end()) {
            LogPrintf("GetHash(): Cache hit for %s\n", search->second.GetHex().c_str());
            return search->second;   // Cache hit
        }
    }
    
    // No cache hit, compute the hash
    returnHash = HashModifiedScrypt(this, V0);
    
    // Store the hash in the cache
    if( useCache ) {
        {
            LOCK(csHashCache);
            LogPrintf("GetHash(): Adding %s to cache\n", returnHash.GetHex().c_str());
            hashCache.insert( std::pair<CBlockHeaderHashKey,uint256>(key,returnHash) );
        }
        AddToDiskBlockHeaderHashCache( *this, returnHash );
    }
    
    return returnHash;
}

uint256 CBlock::BuildMerkleTree(bool* fMutated) const
{
    /* WARNING! If you're reading this because you're learning about crypto
       and/or designing a new system that will use merkle trees, keep in mind
       that the following merkle tree algorithm has a serious flaw related to
       duplicate txids, resulting in a vulnerability (CVE-2012-2459).

       The reason is that if the number of hashes in the list at a given time
       is odd, the last one is duplicated before computing the next level (which
       is unusual in Merkle trees). This results in certain sequences of
       transactions leading to the same merkle root. For example, these two
       trees:

                    A               A
                  /  \            /   \
                B     C         B       C
               / \    |        / \     / \
              D   E   F       D   E   F   F
             / \ / \ / \     / \ / \ / \ / \
             1 2 3 4 5 6     1 2 3 4 5 6 5 6

       for transaction lists [1,2,3,4,5,6] and [1,2,3,4,5,6,5,6] (where 5 and
       6 are repeated) result in the same root hash A (because the hash of both
       of (F) and (F,F) is C).

       The vulnerability results from being able to send a block with such a
       transaction list, with the same merkle root, and the same block hash as
       the original without duplication, resulting in failed validation. If the
       receiving node proceeds to mark that block as permanently invalid
       however, it will fail to accept further unmodified (and thus potentially
       valid) versions of the same block. We defend against this by detecting
       the case where we would hash two identical hashes at the end of the list
       together, and treating that identically to the block having an invalid
       merkle root. Assuming no double-SHA256 collisions, this will detect all
       known ways of changing the transactions without affecting the merkle
       root.
    */
    vMerkleTree.clear();
    vMerkleTree.reserve(vtx.size() * 2 + 16); // Safe upper bound for the number of total nodes.
    for (std::vector<CTransaction>::const_iterator it(vtx.begin()); it != vtx.end(); ++it)
        vMerkleTree.push_back(it->GetHash());
    int j = 0;
    bool mutated = false;
    for (int nSize = vtx.size(); nSize > 1; nSize = (nSize + 1) / 2)
    {
        for (int i = 0; i < nSize; i += 2)
        {
            int i2 = std::min(i+1, nSize-1);
            if (i2 == i + 1 && i2 + 1 == nSize && vMerkleTree[j+i] == vMerkleTree[j+i2]) {
                // Two identical hashes at the end of the list at a particular level.
                mutated = true;
            }
            vMerkleTree.push_back(Hash(BEGIN(vMerkleTree[j+i]),  END(vMerkleTree[j+i]),
                                       BEGIN(vMerkleTree[j+i2]), END(vMerkleTree[j+i2])));
        }
        j += nSize;
    }
    if (fMutated) {
        *fMutated = mutated;
    }
    return (vMerkleTree.empty() ? uint256() : vMerkleTree.back());
}

std::vector<uint256> CBlock::GetMerkleBranch(int nIndex) const
{
    if (vMerkleTree.empty())
        BuildMerkleTree();
    std::vector<uint256> vMerkleBranch;
    int j = 0;
    for (int nSize = vtx.size(); nSize > 1; nSize = (nSize + 1) / 2)
    {
        int i = std::min(nIndex^1, nSize-1);
        vMerkleBranch.push_back(vMerkleTree[j+i]);
        nIndex >>= 1;
        j += nSize;
    }
    return vMerkleBranch;
}

uint256 CBlock::CheckMerkleBranch(uint256 hash, const std::vector<uint256>& vMerkleBranch, int nIndex)
{
    if (nIndex == -1)
        return uint256();
    for (std::vector<uint256>::const_iterator it(vMerkleBranch.begin()); it != vMerkleBranch.end(); ++it)
    {
        if (nIndex & 1)
            hash = Hash(BEGIN(*it), END(*it), BEGIN(hash), END(hash));
        else
            hash = Hash(BEGIN(hash), END(hash), BEGIN(*it), END(*it));
        nIndex >>= 1;
    }
    return hash;
}

std::string CBlock::ToString() const
{
    std::stringstream s;
    s << strprintf("CBlock(hash=%s, ver=%d, hashPrevBlock=%s, hashMerkleRoot=%s, nTime=%u, nBits=%08x, nNonce=%u, vtx=%u)\n",
        GetHash().ToString(),
        nVersion,
        hashPrevBlock.ToString(),
        hashMerkleRoot.ToString(),
        nTime, nBits, nNonce,
        vtx.size());
    for (unsigned int i = 0; i < vtx.size(); i++)
    {
        s << "  " << vtx[i].ToString() << "\n";
    }
    s << "  vMerkleTree: ";
    for (unsigned int i = 0; i < vMerkleTree.size(); i++)
        s << " " << vMerkleTree[i].ToString();
    s << "\n";
    return s.str();
}

void ClearBlockHeaderHashCache(void)
{
    hashCache.clear();
}

void AddToDiskBlockHeaderHashCache(CBlockHeader inBlock, uint256 hash)
{
    LogPrintf("GetHash(): Adding %s to disk cache\n", hash.GetHex().c_str());

    CBlockHeaderHashKey  inHeader(inBlock);

    LOCK( csAddToDisk );

    boost::filesystem::path cacheFileName = GetDataDir() / "blocks/hashcache.dat";
    FILE *file = fopen(cacheFileName.string().c_str(), "ab");
    CAutoFile fileout(file, SER_DISK, CLIENT_VERSION);
    if (fileout.IsNull())
        error("%s: Failed to open file %s", __func__, cacheFileName.string().c_str() );
    
    try {
        fileout << inHeader;
        fileout << hash;
    }
    catch (const std::exception& e) {
        error("%s: Serialize or I/O error - %s", __func__, e.what());
    }
    
    fileout.fclose();
}

bool LoadBlockHeaderHashCache()
{
    CBlockHeaderHashKey   insertHeader;
    uint256               insertHash;
    int64_t               fileSize, numHashes, i;
  
    LogPrintf("LoadBlockHeaderHashCache(): Loading hash cache\n");
    
    hashCache.clear();
    
    boost::filesystem::path cacheFileName = GetDataDir() / "blocks/hashcache.dat";
    FILE *file = fopen(cacheFileName.string().c_str(), "rb");
    CAutoFile filein(file, SER_DISK, CLIENT_VERSION);
    if (filein.IsNull()) {
        LogPrintf("  No hashcache.dat file to load...\n");
        return true;
    }

    fileSize  = boost::filesystem::file_size(cacheFileName);
    numHashes = fileSize / (sizeof(CBlockHeaderHashKey)+sizeof(uint256));

    if( numHashes <= 0 ) {
        LogPrintf("  Invalid hashcache.dat filesize of %lld and numHashes of %lld\n", fileSize, numHashes);
        return false;
    }
    
    if( numHashes * (sizeof(CBlockHeaderHashKey)+sizeof(uint256)) != (uint64_t)fileSize ) {
        LogPrintf("  Warning: hashcache.dat filesize of %lld not valid, deleting cache and letting it rebuild. numHashes %lld sizeof(CBlockHeaderHashKey)+sizeof(uint256) %d\n", fileSize, numHashes, sizeof(CBlockHeaderHashKey)+sizeof(uint256));
        filein.fclose();

        file = fopen(cacheFileName.string().c_str(), "wb");
        CAutoFile filein(file, SER_DISK, CLIENT_VERSION);
        filein.fclose();
        return true;
    }
    
    try {
        for( i = 0; i < numHashes; i++ ) {
            filein >> insertHeader;
            filein >> insertHash;
            hashCache.insert( std::pair<CBlockHeaderHashKey,uint256>(insertHeader,insertHash) );
        }
    }
    
    catch (const std::exception& e) {
        error("%s: Deserialize or I/O error - %s - fileSize %lld, numHashes %lld, i %lld", __func__, e.what(), fileSize, numHashes, i);
        return false;
    }
    
    filein.fclose();

    LogPrintf("LoadBlockHeaderHashCache(): Loaded %lld entries\n", i);
    return true;
}


