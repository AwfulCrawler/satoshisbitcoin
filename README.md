Bitcoin client that full forks to flexible blocksizes
=====================================

This full fork provides an option for Bitcoin users who want to follow Satoshi’s vision of a global peer-to-peer currency that is accessible and usable by everyone. Currently a large number of Bitcoin users want to use a version of Bitcoin that scales as originally intended, but have no option to do. The project is opt-in and only users who want to follow this new branch will do so, users who prefer to stay on the current branch will not be affected. 

Why a full fork?
----------------

Bitcoin was designed by Satoshi as a global peer-to-peer currency accessible and usable by everyone with instantaneous low cost transactions. This vision was clearly laid out in the Bitcoin white paper,  widely understood and agreed by all users and advertised as the vision on the bitcoin.org website and all Bitcoin related forums and websites since 2009. 

Despite this clear vision, Bitcoin is now being artificially constrained to low transaction throughputs well below what the Bitcoin network is capable of supporting. User demand has now reached these artificial constrains and many Bitcoin users are no longer able to use the network and are being denied access.

This artificial change is best described by one of the primary early Bitcoin developers since 2010 in the link below. The reasons are complex but revolve around centralized control. A single company who’s business model develops off-chain solutions now controls Bitcoin development and due to electricity cost advantages mining is no longer performed by the broad user community but by a small number of individuals. As a result, despite the fact that a large majority of Bitcoin users clearly want to scale Bitcoin, those who have taken control refuse to do so.
https://medium.com/@octskyward/the-resolution-of-the-bitcoin-experiment-dabb30201f7

However the strength of Satoshi’s design is users are in control of the system. Any individual user or group of users are able to decide for themselves what Bitcoin should be and which set of rules reflect their preferences. Because of this it is impossible for Bitcoin to ever be centrally controlled, as long as users are able to define for themselves which version of Bitcoin is optimal. 

Additionally, it is hoped that this effort will demonstrate how users are in control of Bitcoin and kick-start multiple different full fork options that offer different multiple options for users and the market to choose from, and that the best option will win in time. In doing so Bitcoin benefits from its open nature and will follow user preferences based on market demand.

What is the full fork and what is being changed?
----------------

The full fork will change the set of rules that define the block chain on a fixed date. After this date a new branch will be created that follows a set of rules that more closely follow Satoshi’s vision. At this point there will be two separate branches of the blockchain and two separate Bitcoins. One branch will follow the existing rules and a new branch will follow the new rules. Each individual user will be able to decide for themselves which branch to follow. The transaction history and BTC owned will be common on both branches up through the fork date, and after that diverge. 

The base client used is Bitcoin Classic version 0.11.2. On top of this version the following rule changes will activate at block height 407232, which is the difficulty adjustment scheduled for mid-April 2016. 
- The block size limit will be removed and replaced with an adjustable limit based on the previous difficulty period’s transaction volume. 
- The POW algorithm will changed 

Note: mid-April 2016 is a target date, the final activation date will depend on development progress which depends on community participation in development as described further below. 

I don't want to fork, will this affect me?
----------------

No. The fork is fully opt-in and people who do not opt-in will not be effected. To use the fork you have to switch your client from an existing client to the Satoshi's Bitcoin client. Only users who switch clients will follow the fork and use the new branch. 

If you continue to use your existing client, you will continue to use the existing blockchain branch and this fork will not affect you in any manner. 

Is this client ready?
----------------

Yes! Intial coding work is complete and several tests have been performed to demonstrate that the client can run on the main net, fork at a specific height, and start to build a new chain using a new block height and POW. Additional development to create a new seed peer list is needed and described below, but all the core functionality needed has been completed.

How will the block size limit be changed?
----------------

The block size limit will be changed to follow the same mechanism as the difficulty for mining. Currently difficulty auto adjusts every 2 weeks and this adjustment is rate limited to only increase or decrease by a factor of 4. 

The block size limit will similarly be set to auto adjust every 2 weeks based on the previous difficulty period’s transaction volume. The new block size limit for the next difficulty period will be reset to 10 times the previous difficulty period’s transaction volume, the adjustment will also be rate limited to only increase or decrease by a factor of 4. 

In this manner the block size limit will function as a spam filter only as originally intended, and transaction throughput can grow based on user demand while providing protection against large block spam attacks. 

Why change the POW algorithm?
----------------

This step is technically required to implement a full fork where a minority of users wishes to break away from the main chain. 

At the fork date it is expected the mining power behind the new fork will be less than the current chain, and as a result the minority chain will not branch and instead continue to follow the larger chain if the same POW is used. By chaining the POW algorithm a hard full fork is set that a minority of users can follow.

Additionally changing the POW algorithm provides an opportunity to re-create a mining ecosystem that more closely follows Satoshi’s vision of one CPU one vote. 

Bitcoin mining centralized because the cost structure of SHA256 mining when fully optimized is heavily dependent of electricity costs. As a result those with access to the lowest cost electricity have an artificial advantage and mining centralizes to the few individuals/firms with the lowest electricity costs. 

Mining specialization and optimization cannot (and should not) be stopped. However it is possible to select and create algorithms that when fully optimized still use more standard hardware and reduce the advantage of low cost electricity. This creates more even competition in mining and by having more even competition encourages a more diverse miner ecosystem with more active user participation.

Changing the POW algorithm also brings back home hobbyist mining, which was a significant driver of Bitcoin’s early interest and adoption. This version of Bitcoin offers hobbyists the opportunity to actively participate in Bitcoin as in Bitcoin’s early days.

Which POW will be used?
----------------

A modified version of scrypt was created and used. 

The overall goal is to take an existing algorithm, and make minor and easy adjustments that significantly reduce the effectiveness of ASIC or GPU implementations. We should still see specialization happen over time, but the optimal point should still create a more balanced environment. 

Based prior experience in creating ASIC and FPGA hardware implementations of existing software algorithms, several characteristics of software algorithms have been identified which are difficult and sub-optimal to implement in hardware, or at least the advantage of a hardware implementation is drastically reduced over a general CPU core. The idea is to start with an existing algorithm and then modify it to have these characterizes. The process and these characteristics are:

- Start with the scrypt algorithm as a base starting point

The goal of scrypt is to force off-chip communication by using more data than can fit onto a single chip. The problem with the Litecoin implementation is the data size selected was much too small and it was possible to develop ASIC cores that required no off-chip communication. 

- Select 128MB as an initial data set size for scrypt 

128MB is well in excess of what can economically fit on a CMOS chip for the foreseeable future and still is reasonable for mid-range clients (cell phones, etc) to process. This number could be set to double every 5 or 10 years. This number can be debated but serves as an initial starting point.

- Change the algorithm to randomize data read from memory

By randomizing the next data element to process, it is not possible to create an efficient ASIC pipeline and instead execution flows in a sequential manner leaving most hardware elements idle. ASICs are only efficient when you have a full pipeline of operations such that every hardware element is performing work in parallel on each clock cycle. Randomizing data breaks this because execution becomes serial such as: a) determine data address, b) fetch data, c) wait long time, d) receive data, e) perform one simple computation, f) determine next data address that is based on e, g) fetch data, h) wait long time, ....

- Change the algorithm to randomize the code path to perform on a given data packet

By performing different code paths on different data packets it is not possible to process data packets in parallel. This makes not just ASIC implementations inefficient, but GPU implementations inefficient as well.

The src/crypto directory contains the code and a detailed explaination/walkthrough. Please review and comment.

What work has been completed?
----------------

The initial release is work and has been tested to successfully fork off of the main net, switch to a new blocksize and POW and build a new independent chain. The repo was forked from Bitcoin Classic 0.11.2 and all changes can be compared to that version.

- Following BIP009 conventions for parallel soft forks, a higher block version byte is used to tag blocks as full fork compatible. Version 0x00000100 (256) is used for the fork.
- The block height for the fork is set to 407232. At this point only blocks tagged for the full fork are accepted
- The block size post-fork automatically increases to 2MB (follows Classic)
- A new DNSSeed server was setup to help forked peers find each other after the fork
- The difficulty adjustment at the fork point is re-set to a value where the expected number of nodes will create blocks every 10 minutes. This is needed because the mining hash rate is unknown, by re-setting the hash rate the branch will effectively work with a small amount of hash power and then self adjust to match the real hash rate the market brings. 
- A POW retargeting overflow bug was found and fixed
- A new modified scrypt POW algorithm was implemented in the crypto library to re-enable CPU mining
- The new POW algorithm activates at the fork height by using the new version tag to select which algorithm
- To improve performance due to how long the new hash algorithm takes (~1 sec / hash), a caching method was implemented to save previous block hashes. 
- Startup performance issues related to the new POW were fixed 
- Multiple performance improves were made to the bitcoind miner
- The band for difficulty adjustments was increased to allow for faster difficulty adjustment in case hash power increases rapidly
- Informational debug.log messaging was improved to better communicate block rejection after the fork
- The alert key was update since it has been compromised by Theymos

What work still needs to be done?
----------------

All development work is complete. The only items remaining are related to helping people find and use the forked client, including:

- Setup a simple satoshisbitcoin.org website
- Create installation binaries for people to install
- Run multiple DNSSeed servers
- Promote the client 

If you are able and interested in helping with any of this please let me know

After the fork what is the long term roadmap?
----------------

This client will follow developments that enable scaling Bitcoin to a large number of transactions so that as many people can use Bitcoin directly as possible. This includes expected developments that reduce block propogation times such as thin blocks, IBLT and sub-chains, amoung others.

Who will control this repo?
----------------

I will maintain control initial but would like to pass off control to established Bitcoin developers who have shown they want to follow the direction in Satoshi's white paper. If this fork is successful and these developers want to take over, I will be happy to pass control back to the early developers who make Bitcoin what it is today and who have refused to follow Blockstream's limited direction.
