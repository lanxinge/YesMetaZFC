import YesMetaZFC.Model.Forcing.Internal.Forcing.Conditions
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # 实际公式的可定义条件集与泛型取见证

可定义性证书携带原 UnarySchema、参数环境及逐值语义证明。泛型引理先应用原分离
公理形成模型集合，再消费泛型性；不对任意外部谓词假定模型内分离。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Defined_d (P : M.Domain → Prop) : Prop :=
  ∃ n, ∃ φ : UnarySchema n, ∃ ρ : Env M n, ∀ p, φ.denote ρ p ↔ P p

def neg_pred_m {k n} (φ : UnarySchema k) (e : Fin k → Term n) (B R z p : Term n) : Formula 1 n :=
  .forallE (.imp (below_m B.weaken R.weaken z.weaken .newest p.weaken)
    (.neg (pred_m φ (fun i => (e i).weaken) .newest)))

@[simp] theorem neg_pred_m_freeClosed {k n} (φ : UnarySchema k) (e : Fin k → Term n)
    (B R z p : Term n) (he : ∀ i, (e i).freeSupport = [])
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hp : p.freeSupport = []) : (neg_pred_m φ e B R z p).FreeClosed := by
  simp -implicitDefEqProofs [neg_pred_m, Definitional.Formula.FreeClosed, *]

theorem neg_pred_sat_l (hE : Extensional M) {k n} (φ : UnarySchema k) (ρ : Env M n)
    (e : Fin k → Term n) (B R z p : Term n) :
    Formula.satisfies ρ (neg_pred_m φ e B R z p) ↔
      Neg_d M (B.eval ρ) (R.eval ρ) (z.eval ρ)
        (φ.denote (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k)) (p.eval ρ) := by
  simp only [neg_pred_m, Neg_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, below_sat_l M hE, pred_sat_l M,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  rfl

theorem defined_set_l (hZF : M.Models ZF) {P : M.Domain → Prop} (h : Defined_d M P) (B : M.Domain) :
    ∃ D, ∀ p, M.mem p D ↔ M.mem p B ∧ P p := by
  obtain ⟨n, φ, ρ, hφ⟩ := h
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ B
  exact ⟨D, fun p => (hD p).trans (and_congr_right fun _ => hφ p)⟩

/-- 判定集使用同一正文与其加强否定，三项条件参数显式加入原参数环境。 -/
theorem defined_decide_l (hE : Extensional M) {P : M.Domain → Prop}
    (h : Defined_d M P) (B R z : M.Domain) :
    Defined_d M (fun p => P p ∨ Neg_d M B R z P p) := by
  obtain ⟨n, φ, ρ, hφ⟩ := h
  let e : Fin n → Term (n + 4) := fun i => .bound ⟨i.val + 4, by omega⟩
  let ψ : UnarySchema (n + 3) := {
    body := .disj (pred_m φ e (.bound 0))
      (neg_pred_m φ e (.bound 3) (.bound 2) (.bound 1) (.bound 0))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, e] }
  let η := ((ρ.push B).push R).push z
  refine ⟨n + 3, ψ, η, fun p => ?_⟩
  have he : (⟨fun i => (e i).eval (η.push p), (η.push p).free⟩ : Env M n) = ρ := by
    cases ρ; rfl
  simp only [UnarySchema.denote, ψ, Formula.satisfies_disj_iff, pred_sat_l M,
    neg_pred_sat_l M hE, he]
  change (φ.denote ρ p ∨ Neg_d M B R z (φ.denote ρ) p) ↔ _
  exact or_congr (hφ p) (forall_congr' fun q => imp_congr_right fun _ => not_congr (hφ q))

theorem eq_force_defined_l (hE : Extensional M) (B R z s t : M.Domain) :
    Defined_d M (fun p => Eq_force_d M B R z p s t) := by
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push s).push t
  let φ : UnarySchema 5 :=
    { body := eq_force_m (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1) }
  exact ⟨5, φ, ρ, fun p => eq_force_sat_l M hE (ρ.push p)
    (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1)⟩

theorem mem_force_defined_l (hE : Extensional M) (B R z s t : M.Domain) :
    Defined_d M (fun p => Mem_force_d M B R z p s t) := by
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push s).push t
  let φ : UnarySchema 5 :=
    { body := mem_force_m (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1) }
  exact ⟨5, φ, ρ, fun p => mem_force_sat_l M hE (ρ.push p)
    (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1)⟩

variable {M} {B R z : M.Domain} {U : M.Domain → Prop}

theorem generic_pick_l (hZF : M.Models ZF) (hU : Generic_d M B R z U)
    {P : M.Domain → Prop} (hP : Defined_d M P) {p} (hp : U p)
    (hd : Dense_d M B R z P p) : ∃ q, U q ∧ P q := by
  obtain ⟨D, hD⟩ := defined_set_l M hZF hP B
  obtain ⟨q, hq, hqD⟩ := hU.meets p hp D (fun q hq => by
    obtain ⟨r, hr, hP⟩ := hd q hq
    exact ⟨r, hr, (hD r).mpr ⟨hr.1, hP⟩⟩)
  exact ⟨q, hq, ((hD q).mp hqD).2⟩

theorem generic_decide_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (hU : Generic_d M B R z U) {P : M.Domain → Prop} (hP : Defined_d M P) :
    (∃ p, U p ∧ P p) ∨ (∃ p, U p ∧ Neg_d M B R z P p) := by
  classical
  obtain ⟨p, hp⟩ := hU.inhabited
  obtain ⟨q, hq, hd⟩ := generic_pick_l hZF hU (defined_decide_l M hZF.1 hP B R z) hp (by
    intro q hq
    by_cases h : ∃ r, Below_d M B R z r q ∧ P r
    · obtain ⟨r, hr, hP⟩ := h
      exact ⟨r, hr, Or.inl hP⟩
    · exact ⟨q, below_refl_l O hq.1 hq.2.1, Or.inr (fun r hr hP => h ⟨r, hr, hP⟩)⟩)
  exact hd.elim (fun h => Or.inl ⟨q, hq, h⟩) (fun h => Or.inr ⟨q, hq, h⟩)

theorem generic_neg_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (hU : Generic_d M B R z U) {P : M.Domain → Prop}
    (hP : Defined_d M P) (hl : Lower_d M B R z P) :
    (∃ p, U p ∧ Neg_d M B R z P p) ↔ ¬ ∃ p, U p ∧ P p := by
  constructor
  · rintro ⟨p, hp, hn⟩ ⟨q, hq, hP⟩
    obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
    have hr' := hU.proper r hr
    exact hn r ⟨hr'.1, hr'.2, hrp⟩ (hl q r (hU.proper q hq).1 ⟨hr'.1, hr'.2, hrq⟩ hP)
  · intro h
    exact (generic_decide_l O hZF hU hP).elim (fun k => False.elim (h k)) id

end YesMetaZFC.Model.Forcing.Internal
