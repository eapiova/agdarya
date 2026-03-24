Displayed type theory
=====================

The combination of flags ``-parametric -arity 1 -direction d -external`` is closely related to `displayed type theory <https://arxiv.org/abs/2311.18781>`_ (dTT), and as such can be selected with the single option ``-dtt``.  The primary differences between ``agdarya -dtt`` and the original dTT of the paper are:

1. Agdarya currently has no modalities, so display can only be applied to closed terms rather than to the more general □-modal ones.
2. Agdarya has symmetries, which in particular (as noted in the paper) makes ``SST⁽ᵈ⁾`` (see :ref:`Displayed coinductive types`) actually usable.
3. As noted above, display in Agdarya computes only up to isomorphism, and in the case of ``Set`` only up to retract up to isomorphism.
4. (A syntactic difference only) Generic degeneracies in Agdarya must be parenthesized, so we write ``A⁽ᵈ⁾`` instead of ``Aᵈ``.

Note that ``-dtt`` does not include ``-discreteness``, but you can add it.
