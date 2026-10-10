import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Atomic
import YesMetaZFC.Model.SetTheory.Internal.TruthRules

/-! # 内部程序行上的 Łoś 归纳性质

归纳对象是模型中的行号，性质是下方给出的实际原公式；赋值族、商赋值和
源真值集都在模型内量化，不以外部标准公式归纳代替内部程序归纳。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_los_d (ω D U p E H C T K F n r : M.Domain) : Prop := ∀ V e Z,
  M.IsSetFunctionFromTo I V D E → M.mem e K → M.PairMember I r Z H → Rp_eval_d I ω D p V e →
    (Rp_holds_d I U V Z ↔ Ssat_d I C T K F n r e)

def rp_los_m {d} (ω D U p E H C T K F n r : Term d) : Formula 1 d := .forallE (.forallE (.forallE
  (.imp (Formula.isFunctionFromTo 𝒞 (.bound 2) D.weaken.weaken.weaken E.weaken.weaken.weaken)
    (.imp (.mem (.bound 1) K.weaken.weaken.weaken)
      (.imp (Formula.orderedPairMem 𝒞 r.weaken.weaken.weaken .newest H.weaken.weaken.weaken)
        (.imp (rp_eval_m (𝒞 := 𝒞) ω.weaken.weaken.weaken D.weaken.weaken.weaken p.weaken.weaken.weaken (.bound 2) (.bound 1))
          (.iff (rp_holds_m (𝒞 := 𝒞) U.weaken.weaken.weaken (.bound 2) .newest)
            (ssat_m (𝒞 := 𝒞) C.weaken.weaken.weaken T.weaken.weaken.weaken K.weaken.weaken.weaken
              F.weaken.weaken.weaken n.weaken.weaken.weaken r.weaken.weaken.weaken (.bound 1)))))))))
derive_free_closed rp_los_m

theorem rp_los_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D U p E H C T K F n r : Term d) :
    Formula.satisfies ρ (rp_los_m (𝒞 := 𝒞) ω D U p E H C T K F n r) ↔
      Rp_los_d I (ω.eval ρ) (D.eval ρ) (U.eval ρ) (p.eval ρ) (E.eval ρ) (H.eval ρ)
        (C.eval ρ) (T.eval ρ) (K.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [rp_los_m, Rp_los_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I,
    rp_eval_sat_l I hE, Formula.satisfies_iff_iff, rp_holds_sat_l I, ssat_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal
