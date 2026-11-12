import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 只以函数图为参数的复合关系

定义域和值域作为公式中的见证。这样原初等图只须搬运三个实际函数码，
不必把两个共同部分中的临界点像额外指定为同一对象。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Cg_d (r s t : M.Domain) : Prop := ∃ a b c, Fn0_d a b r ∧ Fn0_d b c s ∧ Cp0_d a b c r s t

def cg_m {n} (r s t : Term n) : Formula 1 n := set[n] ⟪∃ a b c,
  ⌜fn0_m⌝ₚ(a, b, ⌜r⌝ₛ) ∧ ⌜fn0_m⌝ₚ(b, c, ⌜s⌝ₛ) ∧ ⌜cp0_m⌝ₚ(a, b, c, ⌜r⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ)⟫

derive_free_closed cg_m

theorem cg_sat_l (ext : Extensional M) {n} (ρ : Env M n) (r s t : Term n) :
    Formula.satisfies ρ (cg_m r s t) ↔ Cg_d (r.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [cg_m, Cg_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l ext, cp0_sat_l ext, Definitional.Term.eval_weaken]; rfl

/-- 给定实际两个函数后，图复合就是通常的带定义域复合。 -/
theorem cg_iff_l (ext : Extensional M) {a b c r s t : M.Domain}
    (fr : Fn0_d a b r) (fs : Fn0_d b c s) : Cg_d r s t ↔ Cp0_d a b c r s t := by
  refine ⟨?_, fun h => ⟨a, b, c, fr, fs, h⟩⟩
  rintro ⟨a', b', c', fr', fs', comp⟩
  have eq := fr'.domain_eq_l ext fr
  subst a'
  have eq := fs'.domain_eq_l ext fs
  subst b'
  exact comp.retarget_l fs

variable (I : kpair_convention_l.Interpretation M)

abbrev Rf_comp_d (X R r s t : M.Domain) : Prop :=
  Rr_truth_d I (n := 2) X R (cg_m (.bound 2) (.bound 1) .newest) (Fin.cases t (Fin.cases s (fun _ => r)))

theorem rf_comp_native_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (r s t : (smdl_structure_l I (R := R) nx).Domain) :
    Rf_comp_d I X R r.val s.val t.val ↔ Cg_d r s t :=
  ⟨fun ⟨_, h⟩ => (cg_sat_l ext ..).mp h,
    fun h => ⟨Fin.cases t.property (Fin.cases s.property (fun _ => r.property)), (cg_sat_l ext ..).mpr h⟩⟩

/-- 完整前驱图读取复合，只要求实际六个对象处于其定义域。 -/
theorem rr_graph_comp_l {N R Γ X S k : M.Domain} (nx : ∃ x, M.mem x N) (ny : ∃ x, M.mem x X)
    (ex : Extensional (smdl_structure_l I (R := R) nx)) (ey : Extensional (smdl_structure_l I (R := S) ny))
    (inside : M.MemberSubset Γ N)
    (down : ∀ x y, M.mem x Γ → M.mem y N → M.PairMember I y x R → M.mem y Γ)
    (fk : M.IsSetInjectionFromTo I k Γ X)
    (pred : ∀ x y, M.PairMember I x y k → ∀ z,
      M.PairMember I z y S ↔ ∃ u, M.PairMember I u x R ∧ M.PairMember I u z k)
    (a b c r s t : (smdl_structure_l I (R := R) nx).Domain)
    (a' b' c' r' s' t' : (smdl_structure_l I (R := S) ny).Domain)
    (ha : M.PairMember I a.val a'.val k) (hb : M.PairMember I b.val b'.val k)
    (hc : M.PairMember I c.val c'.val k) (hr : M.PairMember I r.val r'.val k)
    (hs : M.PairMember I s.val s'.val k) (ht : M.PairMember I t.val t'.val k)
    (fr : Fn0_d a b r) (fs : Fn0_d b c s) :
    Cg_d r' s' t' ↔ Cp0_d a b c r s t := by
  let ρ : Env (smdl_structure_l I (R := R) nx) 6 :=
    ⟨Fin.cases t (Fin.cases s (Fin.cases r (Fin.cases c (Fin.cases b (fun _ => a))))), fun _ => a⟩
  let η : Env (smdl_structure_l I (R := S) ny) 6 :=
    ⟨Fin.cases t' (Fin.cases s' (Fin.cases r' (Fin.cases c' (Fin.cases b' (fun _ => a'))))), fun _ => a'⟩
  have move (φ : Formula 1 6) (closed : φ.FreeClosed) (delta : φ.IsDelta0) :=
    rr_graph_delta_l I nx ny ⟨a.val, fk.1.input_mem_of_pairMember ha⟩ inside down fk pred φ closed delta ρ η
      (Fin.cases ht (Fin.cases hs (Fin.cases hr (Fin.cases hc (Fin.cases hb (fun _ => ha))))))
  have fr' : Fn0_d a' b' r' := (fn0_sat_l ey ..).mp
    ((move (fn0_m (.bound 5) (.bound 4) (.bound 2)) (by simp -implicitDefEqProofs) (fn0_delta_l ..)).mp
      ((fn0_sat_l ex ..).mpr fr))
  have fs' : Fn0_d b' c' s' := (fn0_sat_l ey ..).mp
    ((move (fn0_m (.bound 4) (.bound 3) (.bound 1)) (by simp -implicitDefEqProofs) (fn0_delta_l ..)).mp
      ((fn0_sat_l ex ..).mpr fs))
  exact (cg_iff_l ey fr' fs').trans ((cp0_sat_l ey ..).symm.trans
    ((move (cp0_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) (cp0_delta_l ..)).symm.trans (cp0_sat_l ex ..)))

end YesMetaZFC.SetTheory.Internal
