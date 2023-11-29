// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.
//
// File contains modifications by: The Centure developers
// All modifications:
// Copyright (c) 2016-2022 The Centure developers
// Authored by: Malcolm MacLeod (mmacleod@gmx.com)
// Distributed under the GNU Lesser General Public License v3, see the accompanying
// file COPYING

#include "validation.h"
#include "validationinterface.h"
#include "witnessvalidation.h"
#include "versionbitsvalidation.h"
#include <consensus/validation.h>

#include "blockstore.h"
#include "txdb.h"
#include "net.h"
#include "chainparams.h"
#include "versionbits.h"
#include <net_processing.h>

#include <algorithm>

/** Convert CValidationState to a human-readable message for logging */
std::string FormatStateMessage(const CValidationState &state)
{
    return strprintf("%s%s (code %i)",
        state.GetRejectReason(),
        state.GetDebugMessage().empty() ? "" : ", "+state.GetDebugMessage(),
        state.GetRejectCode());
}

/** Return transaction in txOut, and if it was found inside a block, its hash is placed in hashBlock */
bool GetTransaction(const uint256 &hash, CTransactionRef &txOut, const CChainParams& params, uint256 &hashBlock, bool fAllowSlow)
{
    CBlockIndex *pindexSlow = NULL;

    LOCK(cs_main); // Required for ReadBlockFromDisk.

    CTransactionRef ptx = mempool.get(hash);
    if (ptx)
    {
        txOut = ptx;
        return true;
    }

    if (fTxIndex) {
        CDiskTxPos postx;
        if (pblocktree->ReadTxIndex(hash, postx)) {
            CFile file(blockStore.GetBlockFile(postx, true), SER_DISK, CLIENT_VERSION);
            if (file.IsNull())
                return error("%s: OpenBlockFile failed", __func__);
            CBlockHeader header;
            try {
                file >> header;
                fseek(file.Get(), postx.nTxOffset, SEEK_CUR);
                file >> txOut;
            } catch (const std::exception& e) {
                return error("%s: Deserialize or I/O error - %s", __func__, e.what());
            }
            hashBlock = header.GetHashPoW2();
            if (txOut->GetHash() != hash)
                return error("%s: txid mismatch, block hash [%s]", __func__, hashBlock.ToString());
            return true;
        }
    }

    if (fAllowSlow) { // use coin database to locate block that contains transaction, and scan it
        const Coin& coin = AccessByTxid(*pcoinsTip, hash);
        if (!coin.IsSpent()) pindexSlow = chainActive[coin.nHeight];
    }

    if (pindexSlow) {
        CBlock block;
        if (ReadBlockFromDisk(block, pindexSlow, params)) {
            for (const auto& tx : block.vtx) {
                if (tx->GetHash() == hash) {
                    txOut = tx;
                    hashBlock = pindexSlow->GetBlockHashPoW2();
                    return true;
                }
            }
        }
    }

    return false;
}
  
// 1'971'000'000 total supply
// 1'928'950'000 premine
// 10 mining
// 40 holding
// Halving every 4 years

BlockSubsidy GetBlockSubsidy(uint64_t nHeight)
{
    static bool fRegTest = Params().IsRegtest();
    static bool fRegTestLegacy = Params().IsRegtestLegacy();
    static bool fTestnet = Params().IsTestnet();
    if (fTestnet)
        return BlockSubsidy(10*COIN, 10*COIN, 0);

    if (fRegTestLegacy)
        return BlockSubsidy(50*COIN, 0, 0);
    if (fRegTest)
    {
        if (nHeight == 0)
        {
            return BlockSubsidy(50*COIN, 50*COIN, 0*COIN);
        }
        else
        {
            return BlockSubsidy(50*COIN, 50*COIN, 50*COIN);
        }
    }

    CAmount subsidyMining = 10*COIN;
    {
        if (nHeight == 0)
            subsidyMining = (1'931'000'088*COIN)+(18*CENT);

        // Subsidy is cut in half every 400000 blocks(); Which will occur approximately every 4 years.
        // Don't ever shift by more than the bit width (64)
        uint64_t halvings = (int64_t)(nHeight)/400000;
        if (halvings >= 20)
            subsidyMining = 0;
        else
            subsidyMining >>= halvings;
    }
    CAmount subsidyWitness = 40*COIN;
    {
        if (nHeight == 0)
            subsidyWitness = 0*COIN;

        // Subsidy is cut in half every 400000 blocks(); Which will occur approximately every 4 years.
        // Don't ever shift by more than the bit width (64)
        uint64_t halvings = (int64_t)(nHeight)/400000;
        if (halvings >= 20)
            subsidyWitness = 0;
        else
            subsidyWitness >>= halvings;
    }

    return BlockSubsidy(subsidyMining, subsidyWitness, 0);
}

bool IsInitialBlockDownload()
{
    //AssertLockHeld(cs_main);
    const CChainParams& chainParams = Params();

    // Once this function has returned false, it must remain false.
    static std::atomic<bool> latchToFalse{false};
    // Optimization: pre-test latch before taking the lock.
    if (latchToFalse.load(std::memory_order_relaxed))
        return false;

    if (latchToFalse.load(std::memory_order_relaxed))
        return false;
    if (fImporting || fReindex)
        return true;
    if (chainActive.Tip() == NULL)
        return true;
    if (chainActive.Tip()->nChainWork < UintToArith256(chainParams.GetConsensus().nMinimumChainWork))
        return true;
    if (chainActive.Tip()->GetBlockTime() < (GetTime() - nMaxTipAge))
        return true;
    LogPrintf("Leaving InitialBlockDownload (latching to false)\n");
    latchToFalse.store(true, std::memory_order_relaxed);
    return false;
}

bool HaveRequiredPeerUpgradePercent(int nRequiredProtoVersion, unsigned int nRequiredPercent)
{
    std::vector<CNodeStats> vstats;
    g_connman->GetNodeStats(vstats);

    // Insufficient peers to determine.
    if (vstats.size() < 3)
    {
        return true;
    }

    int nUpgradeCount = 0;
    for (const CNodeStats& stats : vstats)
    {
        if (stats.nVersion >= nRequiredProtoVersion)
        {
            ++nUpgradeCount;
        }
    }
    return (100 * nUpgradeCount) / vstats.size() > nRequiredPercent;
}

int32_t ComputeBlockVersion(const CBlockIndex* pindexPrev, const Consensus::Params& params)
{
    LOCK(cs_main);
    int32_t nVersion = VERSIONBITS_TOP_BITS;

    for (int i = 0; i < (int)Consensus::MAX_VERSION_BITS_DEPLOYMENTS; i++)
    {
        ThresholdState state = VersionBitsState(pindexPrev, params, (Consensus::DeploymentPos)i, versionbitscache);
        if (state == THRESHOLD_LOCKED_IN)
        {
            nVersion |= VersionBitsMask(params, (Consensus::DeploymentPos)i);
        }
        else if (state == THRESHOLD_STARTED)
        {
            if (params.vDeployments[i].protoVersion == 0 || HaveRequiredPeerUpgradePercent(params.vDeployments[i].protoVersion, params.vDeployments[i].requiredProtoUpgradePercent))
            {
                nVersion |= VersionBitsMask(params, (Consensus::DeploymentPos)i);
            }
        }
    }

    return nVersion;
}

//! Guess how far we are in the verification process at the given block index
double GuessVerificationProgress(CBlockIndex *pindex) {
    if (pindex == NULL)
        return 0.0;

    double nSyncProgress = std::min(1.0, (double)pindex->nHeight / GetProbableHeight());
    return nSyncProgress;
}

bool GetTxHash(const COutPoint& outpoint, uint256& txHash)
{
    if (outpoint.isHash)
    {
        txHash = outpoint.getTransactionHash();
        return true;
    }
    else
    {
        LOCK(cs_main);
        CBlock block;
        if ((int)outpoint.getTransactionBlockNumber() <= chainActive.Height() && ReadBlockFromDisk(block, chainActive[outpoint.getTransactionBlockNumber()], Params()))
        {
            if (outpoint.getTransactionIndex() < block.vtx.size())
            {
                txHash = block.vtx[outpoint.getTransactionIndex()]->GetHash();
                return true;
            }
        }
    }
    return false;
}
