# RoundingSat

RoundingSat is a pseudo-Boolean SAT solver for optimization and decision problems.

## Compilation

In the root directory of roundingsat:

    cd build
    cmake -DCMAKE_BUILD_TYPE=Release ..
    make

For a debug build:

    cd build_debug
    cmake -DCMAKE_BUILD_TYPE=Debug ..
    make

For more builds, similar build directories can be created.

## SoPlex

RoundingSat supports an integration with the LP solver SoPlex to improve its search routine.
For this, first download SoPlex at https://soplex.zib.de/download.php?fname=soplex-5.0.0.tgz and place the downloaded file in the root directory of roundingsat.
Next, configure with the cmake option `-Dsoplex=ON`:

    cmake -DCMAKE_BUILD_TYPE=Release -Dsoplex=ON ..

Finally, run `make` as normal.
Alternatively, the location of the SoPlex package can also be configured with the cmake option `-Dsoplex_pkg=<location>`.

## Usage

For the input formats, see [here](InputFormats.md).

Download OPB files:

    curl http://www.cril.univ-artois.fr/PB12/bench12/PB12-DEC-SMALLINT-LIN.tar | tar xv

Try on an example instance which is solved quickly:

    bzcat ./PB12/normalized-PB12/DEC-SMALLINT-LIN/sroussel/ShortestPathBA/normalized-BeauxArts_K76.opb.bz2 | ./roundingsat

## Citation

[Elffers and Nordström, 2018] J. Elffers and J. Nordström. Divide and Conquer: Towards Faster Pseudo-Boolean Solving. *IJCAI 2018*, 1291-1299.

## Debug tests with VeriPB

After compiling a debug version, the following executes debug test runs checking runtime invariants, the solver result, and the generated proofs with VeriPB (https://github.com/StephanGocht/VeriPB).

    cd build_debug
    make testruns

Equivalently, execute

    tests/run_tests.sh <timeout> <binary>

to test the given RoundingSat binary with runs using a given timeout.
