# A simple supercompiler formally verified in Agda

This Agda code is based on the work by Dimitur Krustev:

* Dimitur Krustev. A Simple Supercompiler Formally Verified in Coq.  
In Second International Workshop on Metacomputation in Russia
(Proceedings of the Second International Workshop on Metacomputation in Russia.
Pereslavl-Zalessky, Russia, July 1-5, 2010).
A. P. Nemytykh, Ed. - Pereslavl-Zalessky: Ailamazyan University of Pereslavl, 2010, 186 p.
ISBN 978-5-901795-21-7, pages 102-127.  
[https://sites.google.com/site/dkrustev/Home/publications](https://sites.google.com/site/dkrustev/Home/publications)

Files:

* **Everything**. Just imports all other files.

* **Util**. Auxiliary stuff.

* **ExpLang**. A language of expressions. The language of expressions
is "variable free".
All expressions denote functions of type Val → Val,
where Vals are like Lisp S-expressions.

* **PositiveInfo**. Positive information propagation.
We can propagate information about the results of test
inside the branches of a conditional expressions.
This transformation is one of the key differences that distinguish
supercompilation from weaker optimizations like classical
partial evaluation and deforestation.

* **ImpLang**. A small imperative language with assignments
and while-loops.
This language, however, is Turing complete
(unlike the language of expressions).

* **LoopUnrolling**. A simple form of loop unrolling:
trying to execute the body of the loop once before entering the loop,
provided the condition of the loop holds.

* **HomEmb**. The "whistle" of our supercompiler uses
homeomorphic embedding and the Kruskal's tree theorem
to ensure termination of the process. 
To formulate this theorem in its general form,
we introduce a type of arbitrary first-order terms.

* **SimpExpAsFOT**. An injection from language expressions into first-order terms.

* **LoopUnrollingScp**. A simple supercompiler using loop unrolling.

* **Examples**. A few tests and examples.
