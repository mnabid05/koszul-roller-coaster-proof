import Conjectures.RollerFiltrationProducts

/-! Removing a vertex generator from the primal part of the filtration. -/
noncomputable section
namespace RollerFiltration
open Finset RollerRealization RollerVertices RollerFaceMonoid RollerFaceRing
open scoped Classical
variable {p : ℕ} {bs : List Block} (h : ∀ b∈bs, Admissible p b)

def sing (v : W bs p) : F h := ⟨{v},singleton_face h v⟩
def varTerm (v : W bs p) : M h := Term.primal (sing h v)

private theorem var_ok (v : W bs p) (s : F h) (hn : v∉s.val)
    (hf : (complex h).face (insert v s.val)) :
    varTerm h v * Term.primal s = Term.primal (⟨insert v s.val,hf⟩ : F h) := by
  have hd : Disjoint (sing h v).val s.val := Finset.disjoint_singleton_left.mpr hn
  have he : (sing h v).val∪s.val = insert v s.val := by ext w; simp [sing]
  exact (primal_ok (sing h v) s hd (he ▸ hf)).trans (congrArg Term.primal (Subtype.ext he))

private theorem var_bad (v : W bs p) (s : F h)
    (hn : ¬(v∉s.val ∧ (complex h).face (insert v s.val))) :
    varTerm h v * Term.primal s = 0 := by
  apply primal_fail
  rintro ⟨hd,hf⟩
  apply hn
  exact ⟨Finset.disjoint_singleton_left.mp hd,by simpa [sing] using hf⟩

private theorem var_divides (v : W bs p) (s : F h) (hv : v∈s.val) :
    ∃ b, varTerm h v * b = Term.primal s := by
  let f : F h := ⟨s.val.erase v,(complex h).downward (erase_subset ..) s.property⟩
  have he : insert v f.val = s.val := insert_erase hv
  exact ⟨Term.primal f,(var_ok h v f (by simp [f]) (he ▸ s.property)).trans
    (congrArg Term.primal (Subtype.ext he))⟩

theorem vertex_adds {S : Finset (W bs p)} {v : W bs p} (hv : v∈S) (a : M h) :
    a∈vertexIdeal h S ↔ a∈vertexIdeal h (S.erase v) ∨ ∃ b,varTerm h v*b=a := by
  constructor
  · intro ha
    cases a with
    | killed => exact Or.inl trivial
    | dual s => exact Or.inl trivial
    | primal s =>
      obtain ⟨w,hw,hS⟩ := ha
      by_cases eq : w=v
      · exact Or.inr (var_divides h v s (eq ▸ hw))
      · exact Or.inl ⟨w,hw,mem_erase.mpr ⟨eq,hS⟩⟩
  · rintro (ha|⟨b,rfl⟩)
    · cases a with
      | killed => trivial
      | dual s => trivial
      | primal s =>
        obtain ⟨w,hw,hS⟩ := ha
        exact ⟨w,hw,(mem_erase.mp hS).2⟩
    · exact (vertex_closed h S).mul_mem (varTerm h v) ⟨v,mem_singleton_self _,hv⟩ b

theorem vertex_colon {S : Finset (W bs p)} {v : W bs p} (hv : v∉S) (a : M h) :
    a∈vertexIdeal h (neighborsForbidden h S v) ↔ varTerm h v*a∈vertexIdeal h S := by
  cases a with
  | killed => rw [show Term.killed=(0 : M h) from rfl,mul_zero]; rfl
  | dual f =>
    change True ↔ Term.primal (sing h v)*Term.dual f ∈ _
    rw [primal_mul_dual]
    split <;> exact iff_of_true trivial trivial
  | primal f =>
    change hits (neighborsForbidden h S v) f.val ↔ _
    rw [primal_colon_iff hv f.property]
    by_cases hg : v∉f.val ∧ (complex h).face (insert v f.val)
    · rw [var_ok h v f hg.1 hg.2]
      simp only [hg.1,hg.2,not_true_eq_false,false_or]
      rfl
    · rw [var_bad h v f hg]
      exact iff_of_true (by by_cases hvf : v∈f.val; exact Or.inl hvf; exact Or.inr (Or.inl (fun hh => hg ⟨hvf,hh⟩))) trivial

private theorem nonzero_primal_product (S : Finset (W bs p)) (v : W bs p) (a : M h)
    (ha : varTerm h v*a∉vertexIdeal h S) :
    ∃ f : F h, a=Term.primal f ∧ v∉f.val ∧ (complex h).face (insert v f.val) := by
  cases a with
  | killed => exact False.elim (ha (by change _*(0 : M h)∈_; rw [mul_zero]; trivial))
  | dual f =>
    exfalso
    apply ha
    change Term.primal (sing h v)*Term.dual f∈_
    rw [primal_mul_dual]
    split <;> trivial
  | primal f =>
    refine ⟨f,rfl,?_⟩
    by_contra hn
    exact ha (by rw [var_bad h v f hn]; trivial)

theorem vertex_cancel (S : Finset (W bs p)) (v : W bs p) (a b : M h)
    (ha : varTerm h v*a∉vertexIdeal h S) (he : varTerm h v*a=varTerm h v*b) : a=b := by
  have hb := he ▸ ha
  obtain ⟨s,rfl,hs,hu⟩ := nonzero_primal_product h S v a ha
  obtain ⟨t,rfl,ht,hv⟩ := nonzero_primal_product h S v b hb
  rw [var_ok h v s hs hu,var_ok h v t ht hv] at he
  have e : insert v s.val = insert v t.val := congrArg Subtype.val (Term.primal.inj he)
  apply congrArg Term.primal
  exact Subtype.ext (by simpa [hs,ht] using congrArg (fun u : Finset (W bs p) => u.erase v) e)

end RollerFiltration
