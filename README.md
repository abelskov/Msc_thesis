# Master Thesis
This thesis revolves around the reversible programming language Hermes, currently being developed at DIKU as a domain-specific language for implementing symmetric cryptography algorithms on small devices.
The reversibility of Hermes makes us able to give certain guarantees for its safety, in that certain side-channel attacks such as information leakage becomes impossible.
I describe these side-channels as well as reversibility and explain the intention of securing small devices.
I develop a compiler from Hermes to a Reversible Single Static Assignment (RSSA) representation, which could serve as a common ancestor for multiple target assembly languages and help shorten each compilation step to a target assembly language.
I also develop a compiler from RSSA to ARM64 assembly language with abstract register names.
This new implementation gives more control over side-channels as we are no longer dependant on *gcc* and *zerostack*, both of which are being used in the currently existing Hermes to C compiler.
I also implement the 128-bit block cipher algorithm Twofish in Hermes, thereby showing the usefulness of Hermes as a domain-specific language for implementing symmetric cryptographic algorithms.
Finally I compare my Twofish implementation with two reference implementations written in Python and C.
