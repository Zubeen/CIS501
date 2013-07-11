#include <cassert>
#include <cinttypes>
#include <cstdbool>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>

#include <vector>
#include <string>
#include <map>
#include <numeric>
#include <queue>
#include <algorithm>
#include <iostream>
#include <utility>

using namespace std;

const uint64_t INF = 0x7FFFFFFFFFFFFFFF;
const int nPhysicalReg = 2048;
const int N = 8;
bool debug = false;

struct ScoreBoard
{
    vector<int> a;

    ScoreBoard()
    {
        a.resize(nPhysicalReg,0);
    }

    bool isReady(int reg)
    {
        if(reg == -1)
            return true;
        return a[reg] == 0;
    }

    void advanceCycle()
    {
        for(uint32_t i = 0; i < a.size(); i++)
            if(a[i] > 0)
                a[i]--;
    }

    int& operator[](int ind)
    {
        return a[ind];
    }

    void reset()
    {
        for(uint32_t i = 0; i < a.size(); i++)
            a[i] = 0;
    }

} scoreBoard;

struct MicroOp;

struct ROB
{
    uint32_t maxMicroOps;
    deque<MicroOp> q;
    ROB()
    {
       maxMicroOps = 1;
    }

    void reset(int n)
    {
        q.clear();
        maxMicroOps = n;
    }
} rob;

struct MapTable
{
    int mapping[50];
    deque<int> physicalRegsQueue;

    void reset()
    {
        physicalRegsQueue.clear();
        for(int i = 0; i < 50; i++)
            mapping[i] = i;
        for(int i = 50; i < nPhysicalReg; i++)
            physicalRegsQueue.push_back(i);
    }
} mapTable;

struct MicroOp
{
    uint64_t instructionAddress;
    int32_t sourceRegister1;
    int32_t sourceRegister2;
    int32_t destinationRegister;
    char conditionRegister;
    char TNnotBranch;
    char loadStore;
    int64_t immediate;
    uint64_t addressForMemoryOp;
    uint64_t fallthroughPC;
    uint64_t targetAddressTakenBranch; char macroOperation[12];
    char microOperation[23];

    int32_t physicalSrc1;
    int32_t physicalSrc2;
    int32_t physicalSrc3;
    int32_t physicalDest1;
    int32_t physicalDest2;
    int32_t physicalRegToFree1;
    int32_t physicalRegToFree2;

    int32_t archSrc1;
    int32_t archSrc2;
    int32_t archSrc3;
    int32_t archDest1;
    int32_t archDest2;

    bool isLoad, isStore;
    uint64_t age;
    bool issued;
    uint64_t fetchCycle;
    uint64_t issueCycle;
    uint64_t doneCycle;
    uint64_t commitCycle;
    int latency;


    void init(uint64_t instructionAddress, int32_t sourceRegister1, int32_t sourceRegister2,
            int32_t destinationRegister, char conditionRegister, char TNnotBranch, char loadStore,
            int64_t immediate, uint64_t addressForMemoryOp, uint64_t fallthroughPC,
            uint64_t targetAddressTakenBranch, char* macroOperation, char* microOperation, uint64_t age)
    {
       this->instructionAddress = instructionAddress;
       this->sourceRegister1 = sourceRegister1;
       this->sourceRegister2 = sourceRegister2;
       this->destinationRegister = destinationRegister;
       this->conditionRegister = conditionRegister;
       this->TNnotBranch = TNnotBranch;
       this->loadStore = loadStore;
       this->immediate = immediate;
       this->addressForMemoryOp = addressForMemoryOp;
       this->fallthroughPC = fallthroughPC;
       this->targetAddressTakenBranch = targetAddressTakenBranch;
       strcpy(this->macroOperation, macroOperation);
       strcpy(this->microOperation, microOperation);

       archSrc1 = sourceRegister1;
       archSrc2 = sourceRegister2;
       archSrc3 = conditionRegister == 'R' ? 49 : -1;

       archDest1 = destinationRegister;
       archDest2 = conditionRegister == 'W' ? 49 : -1;

       physicalSrc1 = -1;
       physicalSrc2 = -1;
       physicalSrc3 = -1;
       physicalDest1 = -1;
       physicalDest2 = -1;
       physicalRegToFree1 = -1;
       physicalRegToFree2 = -1;

       isLoad = loadStore == 'L';
       isStore = loadStore == 'S';
       this->age = age;
       issued = false;
       fetchCycle = issueCycle = doneCycle = commitCycle = INF;
       latency = 1;
       if(isLoad) latency +=2;
    }

    void reset()
    {
		physicalSrc1 = -1;
		physicalSrc2 = -1;
		physicalSrc3 = -1;
		physicalDest1 = -1;
		physicalDest2 = -1;
		physicalRegToFree1 = -1;
		physicalRegToFree2 = -1;
		fetchCycle = issueCycle = doneCycle = commitCycle = INF;
		issued = false;
    }


    bool isReady()
    {
        if(!scoreBoard.isReady(physicalSrc1) || !scoreBoard.isReady(physicalSrc2) || !scoreBoard.isReady(physicalSrc3))
            return false;

        return true;
    }
};

deque<MicroOp> fetchQueue;

void recoverMOV(uint64_t loadAge, uint64_t currentCycle)
{
    //cout<<"Recovering, currentCycle: "<<currentCycle<<" loadAge: "<<loadAge<<endl;
    while(!rob.q.empty())
    {
        MicroOp m = rob.q.back();
        if(m.age < loadAge)
            break;

        rob.q.pop_back();
        //cout<<"Putting back "<<m.age<<endl;
        if(m.archDest1 != -1)
        {
            int free_reg = mapTable.mapping[m.archDest1];
            mapTable.mapping[m.archDest1] = m.physicalRegToFree1;
            mapTable.physicalRegsQueue.push_front(free_reg);
            scoreBoard[m.physicalDest1] = 0;
            //cout<<"Age:"<<m.age<<" "<<m.physicalDest1<<endl;
        }
        if(m.archDest2 != -1)
        {
            int free_reg = mapTable.mapping[m.archDest2];
            mapTable.mapping[m.archDest2] = m.physicalRegToFree2;
            mapTable.physicalRegsQueue.push_front(free_reg);
            scoreBoard[m.physicalDest2] = 0;
            //cout<<"Age:"<<m.age<<" "<<m.physicalDest2<<endl;
        }
        m.reset();
        fetchQueue.push_front(m);
    }
}

bool fetchMicroOp(FILE *inputFile, MicroOp &m, uint64_t &totalMicroops)
{
    if(!fetchQueue.empty())
    {
        m = fetchQueue.front();
        //cout<<"got "<<m.age<<endl;
        fetchQueue.pop_front();
        return false;;
    }

    int32_t microOpCount;
    uint64_t instructionAddress;
    int32_t sourceRegister1;
    int32_t sourceRegister2;
    int32_t destinationRegister;
    char conditionRegister;
    char TNnotBranch;
    char loadStore;
    int64_t immediate;
    uint64_t addressForMemoryOp;
    uint64_t fallthroughPC;
    uint64_t targetAddressTakenBranch;
    char macroOperation[12];
    char microOperation[23];

    int result = fscanf(inputFile,
            "%" SCNi32
            "%" SCNx64
            "%" SCNi32
            "%" SCNi32
            "%" SCNi32
            " %c"
            " %c"
            " %c"
            "%" SCNi64
            "%" SCNx64
            "%" SCNx64
            "%" SCNx64
            "%11s"
            "%22s",
            &microOpCount,
            &instructionAddress,
            &sourceRegister1,
            &sourceRegister2,
            &destinationRegister,
            &conditionRegister,
            &TNnotBranch,
            &loadStore,
            &immediate,
            &addressForMemoryOp,
            &fallthroughPC,
            &targetAddressTakenBranch,
            macroOperation,
            microOperation);

    if (result == EOF) {
        return true;
    }

    if (result != 14) {
        fprintf(stderr, "Error parsing trace");
        abort();
    }

    m.init(instructionAddress, sourceRegister1, sourceRegister2, destinationRegister,
            conditionRegister, TNnotBranch, loadStore, immediate, addressForMemoryOp,
            fallthroughPC, targetAddressTakenBranch, macroOperation, microOperation, ++totalMicroops);

    //cout<<"read "<<m.age<<endl;
    return false;
}

void renameMicroOp(MicroOp &microOp)
{
    if(microOp.archSrc1 != -1) microOp.physicalSrc1 = mapTable.mapping[microOp.archSrc1];
    if(microOp.archSrc2 != -1) microOp.physicalSrc2 = mapTable.mapping[microOp.archSrc2];
    if(microOp.archSrc3 != -1) microOp.physicalSrc3 = mapTable.mapping[microOp.archSrc3];

    if(microOp.archDest1 != -1)
    {
        microOp.physicalRegToFree1 = mapTable.mapping[microOp.archDest1];
        int new_reg = mapTable.physicalRegsQueue.front(); mapTable.physicalRegsQueue.pop_front();
        mapTable.mapping[microOp.archDest1] = new_reg;
        microOp.physicalDest1 = new_reg;
    }

    if(microOp.archDest2 != -1)
    {
        microOp.physicalRegToFree2 = mapTable.mapping[microOp.archDest2];
        int new_reg = mapTable.physicalRegsQueue.front(); mapTable.physicalRegsQueue.pop_front();
        mapTable.mapping[microOp.archDest2] = new_reg;
        microOp.physicalDest2 = new_reg;
    }
}

bool issue(uint64_t currentCycle)
{
    if(rob.q.empty()) return false;
    int count = 0;
    deque<MicroOp>::iterator itr, itr2;
    for(itr = rob.q.begin(); itr != rob.q.end(); itr++)
    {
        MicroOp &microOp = *itr;
        if(!microOp.issued && microOp.isReady())
        {
            microOp.issued = true;
            microOp.issueCycle = currentCycle;
            microOp.doneCycle = currentCycle + microOp.latency;

            if(microOp.physicalDest1 != -1) scoreBoard[microOp.physicalDest1] = microOp.latency;
            if(microOp.physicalDest2 != -1) scoreBoard[microOp.physicalDest2] = microOp.latency;

            if(++count == N)
                break;
        }

        //execute
        if(microOp.isStore && microOp.doneCycle == currentCycle)
        {
            bool memoryOrderVioldation = false;
            for(itr2 = itr + 1; itr2 != rob.q.end(); itr2++)
            {
                if(itr2->isLoad && itr2->issueCycle <= microOp.issueCycle && itr2->addressForMemoryOp == microOp.addressForMemoryOp)
                {
                    memoryOrderVioldation = true;
                    break;
                }
            }

            if(memoryOrderVioldation)
            {
                recoverMOV(itr2->age, currentCycle);
                return true;
            }
        }
    }
    return false;
}

void commit(uint64_t currentCycle, FILE * outputFile)
{
    for(int i = 0; i < N; i++)
    {
        if(rob.q.empty()) return;

        if(rob.q.front().doneCycle <= currentCycle)
        {
            MicroOp microOp = rob.q.front();
            microOp.commitCycle = currentCycle;
            rob.q.pop_front();

            if(debug)
            {
                fprintf(outputFile, "%"PRIu64": %"PRIu64 " %"PRIu64" %"PRIu64" %"PRIu64, microOp.age, microOp.fetchCycle, microOp.issueCycle,
                        microOp.doneCycle, microOp.commitCycle);

                if(microOp.physicalSrc1 != -1) fprintf(outputFile, ", r%d -> p%d", microOp.archSrc1, microOp.physicalSrc1);
                if(microOp.physicalSrc2 != -1) fprintf(outputFile, ", r%d -> p%d", microOp.archSrc2, microOp.physicalSrc2);
                if(microOp.physicalSrc3 != -1) fprintf(outputFile, ", r%d -> p%d", microOp.archSrc3, microOp.physicalSrc3);

                if(microOp.physicalDest1 != -1) fprintf(outputFile, ", r%d -> p%d [p%d]", microOp.archDest1, microOp.physicalDest1, microOp.physicalRegToFree1);
                if(microOp.physicalDest2 != -1) fprintf(outputFile, ", r%d -> p%d [p%d]", microOp.archDest2, microOp.physicalDest2, microOp.physicalRegToFree2);

                fprintf(outputFile, " | %s %s\n", microOp.macroOperation, microOp.microOperation);
            }

            //cout<<microOp.age<<' '<<microOp.physicalRegToFree1<<' '<<microOp.physicalRegToFree2<<endl;
            if(microOp.physicalRegToFree1 != -1) mapTable.physicalRegsQueue.push_back(microOp.physicalRegToFree1);
            if(microOp.physicalRegToFree2 != -1) mapTable.physicalRegsQueue.push_back(microOp.physicalRegToFree2);
        }
        else return;
    }
}

bool fetchRename(FILE* inputFile, uint64_t currentCycle, uint64_t &totalMicroops)
{
    for(int i = 0; i < N; i++)
    {
        if(rob.q.size() == rob.maxMicroOps)
        {
            //cout<<"rob is full";
            break;
        }

        MicroOp microOp;
        if(fetchMicroOp(inputFile, microOp, totalMicroops))
            return true;

        //cout<<"FetchCycle: "<<currentCycle<<" Age: "<<microOp.age<<endl;
        microOp.fetchCycle = currentCycle;
        renameMicroOp(microOp);
        rob.q.push_back(microOp);
        if(microOp.physicalDest1 != -1) scoreBoard[microOp.physicalDest1] = -1;
        if(microOp.physicalDest2 != -1) scoreBoard[microOp.physicalDest2] = -1;
    }

    return false;
}

void simulate(FILE* inputFile, FILE* outputFile, int size)
{
    uint64_t currentCycle = 0;
    uint64_t totalMicroops = 0;
    rob.reset(size);

    while(true)
    {
        bool eof;
    	commit(currentCycle, outputFile);
        bool skipFetch = issue(currentCycle);
        if(!skipFetch)
            eof = fetchRename(inputFile, currentCycle, totalMicroops);
        currentCycle++;
        scoreBoard.advanceCycle();
        if(eof)
            break;
    }

    while(!rob.q.empty())
    {
        commit(currentCycle, outputFile);
        issue(currentCycle);
        currentCycle++;
        scoreBoard.advanceCycle();
    }
    fprintf(outputFile, "Total cycles: %"PRIu64" Total MicroOps: %"PRIu64 " IPC: %f\n", currentCycle, totalMicroops, double(totalMicroops) / currentCycle);
}

int main(int argc, char *argv[])
{
    int robSize = 128;
    if(argc >= 2)
        sscanf(argv[1], "%d", &robSize);

    scoreBoard.reset();
    mapTable.reset();

    simulate(stdin, stdout, robSize);
    return 0;
}
