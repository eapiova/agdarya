Imports and scoping
===================

File loading
------------

The command ``open import Foo.Bar`` executes the file ``Foo/Bar.ny`` and opens its exported namespace into the current visible scope.  The imported file cannot access definitions from the current file unless it imports them itself.  Importing is not transitive: if ``a.ny`` says ``open import b`` and ``b.ny`` says ``open import c``, then names from ``c`` are not available in ``a`` unless ``a`` also imports ``c`` explicitly.

More precisely, Agdarya tracks both a visible namespace and an export namespace.  ``open import`` only affects the visible namespace, while ``open import … public`` affects both: the imported names become visible in the current file and are also re-exported to later importers of the current file.  The analogous rule holds for ``open M`` versus ``open M public`` on an already visible module path ``M``.

By contrast, when in interactive mode or executing a command-line ``-e`` string, all definitions from files and strings explicitly specified earlier on the command line are available, even if they were not re-exported.  This does not carry over transitively through further imports.  Standard input (indicated by ``-`` on the command line) is treated as an ordinary file; thus it must import any files it wants to use, but its definitions are automatically available to later ``-e`` strings and interactive commands.

No file is executed more than once during a single run, even if it is imported multiple times.  Thus, if both ``b.ny`` and ``c.ny`` say ``open import d``, and ``a.ny`` imports both ``b`` and ``c``, then effectful commands such as ``echo`` in ``d.ny`` happen only once, there is only one copy of ``d``'s exported names in the visible namespace of ``a.ny``, and the definitions seen through ``b`` and ``c`` are compatible.  Circular imports are rejected.  Execution still follows the command-line order together with depth-first traversal of imports as they are encountered.

.. _Namespaces and sections:

Namespaces and modules
----------------------

Agdarya uses `Yuujinchou <https://redprl.org/yuujinchou/yuujinchou/>`_ for hierarchical namespacing, with periods separating namespace components.  Thus a name such as ``nat.plus`` lies in the namespace ``nat``.  You can define such a constant directly:

.. code-block:: none

   nat.plus : A
   nat.plus = BODY

More commonly, you group related definitions with a module declaration:

.. code-block:: none

   module nat where {
     plus : A;
     plus = BODY
   }

This defines the constant ``nat.plus``.  Before layout is added in :ref:`A8`, module bodies use explicit braces and semicolons.  Modules can be nested, and they can also be parameterized:

.. code-block:: none

   module NatOps (A : Set) where {
     id : A → A;
     id x = x
   }

   module NatIds = NatOps ℕ

The command ``open nat`` opens an already visible module path into the current visible namespace.  This makes names such as ``plus`` available unqualified while leaving their qualified names such as ``nat.plus`` available as well.  Using ``public`` on ``open`` re-exports the opened names.

Inside a module, ``private`` keeps a declaration visible within the module body but omits it from the module's exported namespace:

.. code-block:: none

   module M where {
     private postulate hidden : Set;
     postulate visible : Set
   }

After this, ``M.visible`` is available outside the module, while ``M.hidden`` is not.


.. _Import modifiers:

Open modifiers
--------------

Both ``open`` and ``open import`` accept a small family of namespace modifiers:

- ``using (x; y; foo.bar)`` keeps only the listed names or subtrees.
- ``hiding (x; foo.bar)`` keeps everything except the listed names or subtrees.
- ``renaming (x to y; foo.bar to baz.qux)`` renames names or subtrees after the previous filtering step.

At most one of ``using`` and ``hiding`` may appear, followed optionally by ``renaming``.  For example:

.. code-block:: none

   open import Nat using (zero; suc)
   open import Nat hiding (notations)
   open import Nat using (nums.two) renaming (nums.two to two)
   open M public renaming (B to C)

There is no separate ``import`` / ``export`` command anymore, and the older Yuujinchou modifier DSL (such as ``| only``, ``| except``, ``| seq``, and ``| union``) is not part of the public surface syntax.


Importing notations
-------------------

Visibility of notations defined by another file or module is implemented as a special case of opening names.  When a new notation is declared, it is associated to a generated name in the current namespace prefixed by ``notations``.  For instance,

.. code-block:: none

   notation(1) x "+" y ≔ plus x y

creates a notation name under ``notations``.

This means that notation visibility is controlled by the same ``using`` / ``hiding`` / ``renaming`` machinery as ordinary names.  For example:

.. code-block:: none

   open import Nat using (notations)
   open Nat hiding (notations)

The ``notations`` subtree is not otherwise special on the naming side: it is an ordinary namespace subtree that the parser consults when deciding which notations are in scope.  In practice, if you want imported definitions to remain qualified while still exposing selected notation subtrees, the most robust A7 approach is to place the definitions inside modules and then ``open`` only the parts you want.


Compilation
-----------

Whenever a file ``FILE.ny`` is successfully executed, Agdarya writes a "compiled" version of that file in the same directory called ``FILE.nyo``.  Then in future runs of Agdarya, whenever ``FILE.ny`` is to be executed, if

1. ``-source-only`` was not specified,
2. ``FILE.ny`` was not specified explicitly on the command-line (so that it must have been imported by another file),
3. ``FILE.nyo`` exists in the same directory,
4. the same type theory flags (``-parametric``, ``-arity``, ``-direction``, ``-internal``/``-external``, and ``-discreteness``) are in effect now as when ``FILE.nyo`` was compiled,
5. ``FILE.ny`` has not been modified more recently than ``FILE.nyo``, and
6. none of the files imported by ``FILE.ny`` are newer than it or their compiled versions,

then ``FILE.nyo`` is loaded directly instead of re-executing ``FILE.ny``, skipping the typechecking step.  This can be much faster.  If any of these conditions fail, then ``FILE.ny`` is executed from source as usual, and a new compiled version ``FILE.nyo`` is saved, overwriting the previous one.

Effectual commands like ``echo`` are *not* re-executed when a file is loaded from its compiled version (they are not even stored in the compiled version).  Since this may be surprising, Agdarya issues a warning when loading a compiled version of a file that originally contained ``echo`` commands.  Since files explicitly specified on the command-line are never loaded from a compiled version, the best way to avoid this warning is to avoid ``echo`` statements in "library" files that are intended to be imported by other files.  Of course, you can also use ``-source-only`` to prevent all loading from compiled files.
