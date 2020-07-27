# RoundingSat

RoundingSat is a pseudo-Boolean SAT solver for optimization and decision problems.

## Compilation

In the root directory of RoundingSat:

    cd build
    cmake -DCMAKE_BUILD_TYPE=Release ..
    make

For a debug build:

    cd build_debug
    cmake -DCMAKE_BUILD_TYPE=Debug ..
    make

For more builds, similar build directories can be created.

## Dependencies

- C++17 (i.e., a reasonably recent compiler)
- Boost library: https://www.boost.org
- Optionally: SoPlex LP solver (see below)

## SoPlex

RoundingSat supports an integration with the LP solver SoPlex to improve its search routine.
For this, first download SoPlex at https://soplex.zib.de/download.php?fname=soplex-5.0.1.tgz and place the downloaded file in the root directory of RoundingSat.
Next, follow the above build process, but configure with the cmake option `-Dsoplex=ON`:

    cd build
    cmake -DCMAKE_BUILD_TYPE=Release -Dsoplex=ON ..
    make

The location of the SoPlex package can be configured with the cmake option `-Dsoplex_pkg=<location>`.

## Usage

RoundingSat takes as input a linear Boolean formula / 0-1 integer linear program, and outputs a(n optimal) solution or reports that none exists.
Either pipe the formula to RoundingSat

    cat test/instances/opb/opt/stein15.opb | build/roundingsat

or pass the file as a parameter

    build/roundingsat test/instances/opb/opt/stein15.opb

RoundingSat supports three input formats:
- pseudo-Boolean PBO format (only linear objective and constraints)
- DIMACS CNF (conjunctive normal form)
- Weighted CNF

For a description of these input formats, see [here](InputFormats.md).

## Citation

[Elffers and Nordström, 2018] J. Elffers and J. Nordström. Divide and Conquer: Towards Faster Pseudo-Boolean Solving. *IJCAI 2018*, 1291-1299.

## Debug tests with VeriPB

After compiling a debug version, the following executes debug test runs checking runtime invariants, the solver result, and the generated proofs with VeriPB (https://github.com/StephanGocht/VeriPB).

    cd build_debug
    make testruns

Equivalently, execute

    tests/run_tests.sh <timeout> <binary>

to test the given RoundingSat binary with runs using a given timeout.
