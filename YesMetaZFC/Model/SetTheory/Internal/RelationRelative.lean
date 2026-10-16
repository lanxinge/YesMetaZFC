import YesMetaZFC.Model.SetTheory.Internal.Source
import YesMetaZFC.Model.SetTheory.Internal.Structure
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Construction

/-! # 原公式在任意编码关系模型中的相对化

成员关系读原关系图，量词限于原载体，定义原子也按该关系展开。
此解释不把商对象当作背景集合，不要求关系良基或载体传递。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention}

def rr_rel_m (𝒞 : OrderedPairConvention) : {n d : Nat} → Formula 1 n → Term d → Term d → (Fin n → Term d) → Formula 1 d
  | _, _, .falsum, _, _, _ => .falsum
  | _, _, .truth, _, _, _ => .truth
  | _, _, .mem s t, _, R, e => Formula.orderedPairMem 𝒞 (s.bind e) (t.bind e) R
  | _, _, .atom .extensionalEq _ ts, X, R, e => Formula.forallMem X
      (.iff (Formula.orderedPairMem 𝒞 .newest ((ts 0).bind e).weaken R.weaken)
        (Formula.orderedPairMem 𝒞 .newest ((ts 1).bind e).weaken R.weaken))
  | _, _, .atom .subset _ ts, X, R, e => Formula.forallMem X
      (.imp (Formula.orderedPairMem 𝒞 .newest ((ts 0).bind e).weaken R.weaken)
        (Formula.orderedPairMem 𝒞 .newest ((ts 1).bind e).weaken R.weaken))
  | _, _, .neg φ, X, R, e => .neg (rr_rel_m 𝒞 φ X R e)
  | _, _, .conj φ ψ, X, R, e => .conj (rr_rel_m 𝒞 φ X R e) (rr_rel_m 𝒞 ψ X R e)
  | _, _, .disj φ ψ, X, R, e => .disj (rr_rel_m 𝒞 φ X R e) (rr_rel_m 𝒞 ψ X R e)
  | _, _, .imp φ ψ, X, R, e => .imp (rr_rel_m 𝒞 φ X R e) (rr_rel_m 𝒞 ψ X R e)
  | _, _, .iff φ ψ, X, R, e => .iff (rr_rel_m 𝒞 φ X R e) (rr_rel_m 𝒞 ψ X R e)
  | _, _, .existsE φ, X, R, e => Formula.existsMem X
      (rr_rel_m 𝒞 φ X.weaken R.weaken (Fin.cases .newest (fun i => (e i).weaken)))
  | _, _, .forallE φ, X, R, e => Formula.forallMem X
      (rr_rel_m 𝒞 φ X.weaken R.weaken (Fin.cases .newest (fun i => (e i).weaken)))

@[simp] theorem rr_rel_closed_l (𝒞 : OrderedPairConvention) {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed) (X R : Term d) (e : Fin n → Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) :
    (rr_rel_m 𝒞 φ X R e).FreeClosed := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => trivial
  case mem s t =>
    simp only [rr_rel_m]
    exact Formula.orderedPairMem_freeClosed 𝒞 _ _ _
      ((Definitional.Term.freeSupport_bind_of_closed e he s).trans hφ.1)
      ((Definitional.Term.freeSupport_bind_of_closed e he t).trans hφ.2) hR
  case atom r hr ts =>
    have h0 := (Definitional.Term.freeSupport_bind_of_closed e he (ts 0)).trans (hφ 0)
    have h1 := (Definitional.Term.freeSupport_bind_of_closed e he (ts 1)).trans (hφ 1)
    cases r <;> simp -implicitDefEqProofs [rr_rel_m, Formula.forallMem, Definitional.Formula.FreeClosed, hX, hR, h0, h1]
  case neg φ ih => exact ih hφ X R e hX hR he
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    exact ⟨ih hφ.1 X R e hX hR he, jh hφ.2 X R e hX hR he⟩
  case existsE φ ih | forallE φ ih =>
    exact ⟨⟨rfl, by simpa using hX⟩, ih hφ X.weaken R.weaken _ (by simpa using hX)
      (by simpa using hR) (Fin.cases rfl (fun i => by simpa using he i))⟩

theorem rr_rel_sat_l (I : 𝒞.Interpretation M) {X R : M.Domain}
    (nx : ∃ x, M.mem x X) {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) nx) n) (θ : Env M d) (T S : Term d) (e : Fin n → Term d)
    (hT : T.eval θ = X) (hS : S.eval θ = R) (he : ∀ i, (e i).eval θ = (ρ.bound i).val) :
    Formula.satisfies θ (rr_rel_m 𝒞 φ T S e) ↔ Formula.satisfies ρ φ := by
  have term {n d} (ρ : Env (smdl_structure_l I (R := R) nx) n) (θ : Env M d) (e : Fin n → Term d)
      (he : ∀ i, (e i).eval θ = (ρ.bound i).val) (t : Term n) (ht : t.freeSupport = []) :
      (t.bind e).eval θ = (t.eval ρ).val := by
    cases t with
    | free _ => simp at ht
    | bound i => exact he i
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [rr_rel_m, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff]
  case mem s t =>
    simp only [rr_rel_m, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff,
      term ρ θ e he s hφ.1, term ρ θ e he t hφ.2, hS]
    rfl
  case atom r hr ts =>
    cases r <;> simp only [rr_rel_m, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_atom_extensionalEq_iff,
      Formula.satisfies_atom_subset_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
      term ρ θ e he (ts 0) (hφ 0), term ρ θ e he (ts 1) (hφ 1), hT, hS]
    all_goals exact ⟨fun h x => h x.val x.property, fun h x hx => h ⟨x, hx⟩⟩
  case neg φ ih => exact not_congr (ih hφ ρ θ T S e hT hS he)
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [rr_rel_m, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, ih hφ.1 ρ θ T S e hT hS he, jh hφ.2 ρ θ T S e hT hS he]
  case existsE φ ih | forallE φ ih =>
    have tr (x : (smdl_structure_l I (R := R) nx).Domain) := ih hφ (ρ.push x) (θ.push x.val) T.weaken S.weaken
      (Fin.cases .newest (fun i => (e i).weaken)) (by simpa using hT) (by simpa using hS)
      (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken θ x.val (e i)).trans (he i)))
    first
    | rw [rr_rel_m, Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, hT]
      exact ⟨fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, (tr ⟨x, hx⟩).mp h⟩, fun ⟨x, h⟩ => ⟨x.val, x.property, (tr x).mpr h⟩⟩
    | rw [rr_rel_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, hT]
      exact ⟨fun h x => (tr x).mp (h x.val x.property), fun h x hx => (tr ⟨x, hx⟩).mpr (h ⟨x, hx⟩)⟩

end YesMetaZFC.SetTheory.Internal
