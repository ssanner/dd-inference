add-gen Package
Generic Version of the add package, allowing use
of different data kinds for the algebraic values of the Affine ADD.

Notes:
Gen is the abstract class that must be implemented by data implementations.
Gen variables usually start with _a (algebraic instead of _d double)

the DAADD is the double version of AADD, and so are DAADDNodes.

AADD constructor can receive extra integer parameters to determine data kind and hash function.
