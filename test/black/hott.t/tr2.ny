postulate A00 : Set
postulate A01 : Set
postulate A02 : Id Set A00 A01
postulate A10 : Set
postulate A11 : Set
postulate A12 : Id Set A10 A11
postulate A20 : Id Set A00 A10
postulate A21 : Id Set A01 A11
postulate A22 : Set⁽ᵉᵉ⁾ A02 A12 A20 A21

postulate a00 : A00
postulate a01 : A01
postulate a02 : A02 a00 a01
postulate a10 : A10
postulate a11 : A11
postulate a12 : A12 a10 a11
postulate a20 : A20 a00 a10
postulate a21 : A21 a01 a11

synth A22 trr⟨1⟩
synth A22 trr⟨1⟩ a02
synth A20 trr⟨1⟩ a00
synth A21 trr⟨1⟩ a01

synth A22 liftr⟨1⟩
synth A22 liftr⟨1⟩ a02
synth A20 liftr⟨1⟩ a00
synth A21 liftr⟨1⟩ a01

synth A22 trl⟨1⟩
synth A22 trl⟨1⟩ a12
synth A20 trl⟨1⟩ a10
synth A21 trl⟨1⟩ a11

synth A22 trr⟨2⟩
synth A22 trr⟨2⟩ a20
echo A22 trr⟨2⟩ a20
synth A02 trr⟨1⟩ a00
synth A12 trr⟨1⟩ a10

synth A22 liftr⟨2⟩
synth A22 liftr⟨2⟩ a20
echo A22 liftr⟨2⟩ a20
synth sym A22 trr⟨1⟩ a20
synth A02 trr⟨1⟩ a00
synth A12 trr⟨1⟩ a10
synth A02 liftr⟨1⟩ a00
synth A12 liftr⟨1⟩ a10

synth A22 a02 a12 trr⟨1⟩
synth A22 a02 a12 trr⟨1⟩ a20
synth A22 a02 a12 liftr⟨1⟩ a20

synth A22 a02 a12 trl⟨1⟩
synth A22 a02 a12 trl⟨1⟩ a21
synth A22 a02 a12 liftl⟨1⟩ a21

synth sym A22 a20 a21 trr⟨1⟩
synth sym A22 a20 a21 trr⟨1⟩ a02
synth sym (sym A22 a20 a21 liftr⟨1⟩ a02)

synth sym A22 a20 a21 trl⟨1⟩
synth sym A22 a20 a21 trl⟨1⟩ a12
synth sym (sym A22 a20 a21 liftl⟨1⟩ a12)
