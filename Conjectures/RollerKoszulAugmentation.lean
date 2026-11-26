import Conjectures.RollerBasedKoszul
import Conjectures.RollerKoszulMultilinear

/-! The normalized bar differential over the field, evaluated as an alternating
sum of products in the actual algebra on tensor words in its augmentation ideal. -/
noncomputable section
open scoped Classical

namespace RollerKoszul.Bar
variable {S T K : Type*} [Semigroup S] [Semigroup T] [AddCommGroup K]

/-- Alternately contract the adjacent pairs in a single tensor word. -/
def adjacent (f : List S → K) : List S → K
  | [] => 0
  | a::l => -internal (fun b w => f (b::w)) a l

private theorem internal_map (p : S → T) (hp : ∀ a b, p (a*b)=p a*p b)
    (f : T → List T → K) (a : S) (l : List S) :
    internal f (p a) (l.map p) =
      internal (fun b w => f (p b) (w.map p)) a l := by
  induction l generalizing a f with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,internal,hp]; rw [ih]

theorem adjacent_map (p : S → T) (hp : ∀ a b, p (a*b)=p a*p b)
    (f : List T → K) (l : List S) : adjacent f (l.map p) =
      adjacent (fun w => f (w.map p)) l := by
  cases l with
  | nil => rfl
  | cons a l => exact congrArg Neg.neg (internal_map p hp _ a l)

end RollerKoszul.Bar

namespace RollerKoszul.AlgebraBarWitness

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {P : ℕ → Submodule K A}
variable {S : Type} [MonoidWithZero S] [Fintype S] (W : AlgebraBarWitness K A P S)

abbrev augmentationIdeal := LinearMap.ker W.augmentation.toLinearMap

private def project (a : A) : W.augmentationIdeal :=
  ⟨a - algebraMap K A (W.augmentation a),by simp [LinearMap.mem_ker]⟩

private theorem project_basis (v : W.PositiveIndex) :
    W.project (W.value v.val) = W.positiveBasis v := by
  apply Subtype.ext
  have hz := (W.positiveBasis v).property
  rw [LinearMap.mem_ker] at hz
  change W.augmentation (W.positiveBasis v).val=0 at hz
  rw [W.positiveBasis_apply] at hz
  change W.value v.val - algebraMap K A (W.augmentation (W.value v.val)) = _
  rw [hz,map_zero,sub_zero,W.positiveBasis_apply]

/-- Evaluate an n-linear form on a word of algebra elements after projection onto
the augmentation ideal. Words of other lengths have value zero. -/
def applyForm {n : ℕ} (F : MultilinearMap K (fun _ : Fin n => W.augmentationIdeal) K)
    (l : List A) : K :=
  if h : l.length=n then F (fun i => W.project (l.get (Fin.cast h.symm i))) else 0

private theorem applyForm_ofFn {n : ℕ} (F : MultilinearMap K (fun _ : Fin n => W.augmentationIdeal) K)
    (u : Fin n → A) : W.applyForm F (List.ofFn u) = F (fun i => W.project (u i)) := by
  simp [applyForm,List.get_ofFn]

def atomValue (a : W.degree.Atom) : A := W.value a.val

private theorem atomValue_mul (a b : W.degree.Atom) :
    W.atomValue (a*b) = W.atomValue a * W.atomValue b := map_mul W.value a.val b.val

/-- The homogeneous cochain is realized on *every* word by its corresponding
multilinear form, also when a letter represents an algebra product that vanishes. -/
theorem actual_form {n d : ℕ} (f : W.degree.wordCochains K n d) (w : List W.degree.Atom) :
    W.applyForm (W.degree.formEquiv W.positiveBasis n d f).val (w.map W.atomValue) = f.val w := by
  let F := (W.degree.formEquiv W.positiveBasis n d f).val
  by_cases hl : w.length=n
  · let u : Fin n → W.degree.Atom := fun i => w.get (Fin.cast hl.symm i)
    have hu : List.ofFn u=w := by
      subst n
      exact List.ofFn_get w
    rw [← hu,List.map_ofFn,W.applyForm_ofFn]
    by_cases hn : ∀ i, (u i).val≠0
    · let v (i : Fin n) : W.PositiveIndex :=
        ⟨(u i).val,hn i,(show (u i).val=0 ∨ 0<W.degree.degree (u i).val
          from (u i).property).resolve_left (hn i)⟩
      have he : (fun i => W.project ((W.atomValue ∘ u) i)) = fun i => W.positiveBasis (v i) :=
        funext fun i => W.project_basis (v i)
      rw [he]
      exact W.degree.formEquiv_apply W.positiveBasis f v
    · obtain ⟨i,hi⟩ : ∃ i, (u i).val=0 := by simpa only [not_forall,not_not] using hn
      have hp : W.project ((W.atomValue ∘ u) i) = 0 := by
        apply Subtype.ext; simp [atomValue,project,hi]
      rw [MultilinearMap.map_coord_zero _ i hp]
      symm
      apply Classical.byContradiction
      intro h
      have hz := (f.property _ h).1
      exact hz (List.mem_map.mpr ⟨u i,List.mem_ofFn.mpr ⟨i,rfl⟩,hi⟩)
  · rw [applyForm,dif_neg (by simpa using hl)]
    symm
    exact Classical.byContradiction (fun h => hl (f.property _ h).2.1)

/-- The differential on coordinates equals the ordinary reduced bar differential
using multiplication in the actual algebra, term for term. -/
theorem actual_differential {n d : ℕ} (f : W.degree.wordCochains K n d)
    (w : List W.degree.Atom) :
    Bar.adjacent (W.applyForm (W.degree.formEquiv W.positiveBasis n d f).val)
      (w.map W.atomValue) = W.degree.reduced f.val w := by
  rw [Bar.adjacent_map W.atomValue W.atomValue_mul,show
    (fun l => W.applyForm (W.degree.formEquiv W.positiveBasis n d f).val (l.map W.atomValue)) =
    f.val from funext (W.actual_form f)]
  cases w <;> rfl

/-- In positive cohomological degree off the diagonal, every homogeneous cocycle of
multilinear forms on the actual augmentation ideal is a coboundary. The identities
are tested on tensor basis words and all intermediate products take place in A. -/
theorem actual_exact {n d : ℕ} (hnd : n+1≠d)
    (F : W.degree.formSpace W.positiveBasis (n+1) d)
    (closed : ∀ w : List W.degree.Atom, Bar.adjacent (W.applyForm F.val) (w.map W.atomValue) = 0) :
    ∃ H : W.degree.formSpace W.positiveBasis n d, ∀ w : List W.degree.Atom,
      Bar.adjacent (W.applyForm H.val) (w.map W.atomValue) =
        W.applyForm F.val (w.map W.atomValue) := by
  letI : Nontrivial A := ⟨⟨0,1,fun h => zero_ne_one (α := K)
    (W.augmentation.map_zero.symm.trans ((congrArg W.augmentation h).trans W.augmentation.map_one))⟩⟩
  letI : Nontrivial S := ⟨⟨0,1,fun h => zero_ne_one (α := A)
    (W.value.map_zero.symm.trans ((congrArg W.value h).trans W.value.map_one))⟩⟩
  let f := (W.degree.formEquiv W.positiveBasis (n+1) d).symm F
  have hf : W.degree.formEquiv W.positiveBasis (n+1) d f = F :=
    (W.degree.formEquiv W.positiveBasis (n+1) d).apply_symm_apply F
  have hclosed : ∀ w, W.degree.reduced f.val w = 0 := fun w => by
    rw [← W.actual_differential f w,hf]
    exact closed w
  obtain ⟨h,hh⟩ := W.degree.reduced_exact W.diagonal (n+1) d hnd f hclosed
  refine ⟨W.degree.formEquiv W.positiveBasis n d h,fun w => ?_⟩
  rw [W.actual_differential,← hf,W.actual_form,hh]

end RollerKoszul.AlgebraBarWitness
