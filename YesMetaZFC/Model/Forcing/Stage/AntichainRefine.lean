import YesMetaZFC.Model.Forcing.Stage.AntichainDense
import YesMetaZFC.SetTheory.DependentChoice

/-! # 稠密细化保留原反链的大小

细化条件若与原反链元素相容，就已经在该元素以下。这样，原反链每个元素
都可选到一个不同的细化元素，得到模型内单射。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC) {B R z : M.Domain}
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem antichain_refine_l (O : Cond_order_d M B R z) {p D A : M.Domain} (hp : M.mem p B)
    (dense : Dense_d M B R z (fun q => M.mem q D) p) (anti : Antichain_d M B R z A)
    (below : ∀ a, M.mem a A → Below_d M B R z a p) : ∃ C F,
      Antichain_d M B R z C ∧ (∀ c, M.mem c C → M.mem c D ∧ Below_d M B R z c p) ∧
      (∀ q, Below_d M B R z q p → ∃ c, M.mem c C ∧ Cmp_d M B R z q c) ∧
      M.IsSetInjectionFromTo I F A C ∧ (∀ a c, Entry_d M a c F → Entry_d M c a R) := by
  classical
  let ρ : Env M 4 := ⟨fun i => [B,R,z,A].get i,fun _ => p⟩
  let φ : UnarySchema 4 := { body := set[5] ⟪∀ a ∈ ⌜(.bound 4 : Term 5)⌝ₛ,
    ⌜cmp_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ,⌜(.bound 2 : Term 5)⌝ₛ,⌜(.bound 3 : Term 5)⌝ₛ,⌜(.newest : Term 5)⌝ₛ,a) →
      ⌜entry_m⌝ₚ(⌜(.newest : Term 5)⌝ₛ,a,⌜(.bound 2 : Term 5)⌝ₛ)⟫ }
  obtain ⟨E,members⟩ := ZF.separation_exists_d hZF φ ρ D
  have member c : M.mem c E ↔ M.mem c D ∧ ∀ a, M.mem a A → Cmp_d M B R z c a → Entry_d M c a R := by
    apply (members c).trans (and_congr_right fun _ => ?_)
    simp only [φ,Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,cmp_sat_l M hZFC.1,
      entry_sat_l M hZFC.1,Definitional.Term.eval_weaken]
    rfl
  have denseE : Dense_d M B R z (fun c => M.mem c E) p := by
    intro q hq
    by_cases hit : ∃ a, M.mem a A ∧ Cmp_d M B R z q a
    · obtain ⟨a,ha,t,ht,ta⟩ := hit
      obtain ⟨r,hr,rd⟩ := dense t (below_trans_l O hp ht hq)
      have ra := O.trans r t a hr.1 ht.1 (anti.1 a ha).1 hr.2.2 ta
      refine ⟨r,below_trans_l O hq.1 hr ht,(member r).mpr ⟨rd,fun b hb compat => ?_⟩⟩
      obtain ⟨s,hs,sb⟩ := compat
      have ab := anti.2 a b ha hb ⟨s,⟨hs.1,hs.2.1,O.trans s r a hs.1 hr.1 (anti.1 a ha).1 hs.2.2 ra⟩,sb⟩
      exact ab ▸ ra
    · obtain ⟨r,hr,rd⟩ := dense q hq
      refine ⟨r,hr,(member r).mpr ⟨rd,fun a ha compat => ?_⟩⟩
      obtain ⟨s,hs,sa⟩ := compat
      exact (hit ⟨a,ha,s,below_trans_l O hq.1 hs hr,sa⟩).elim
  obtain ⟨C,antiC,bound,maximal⟩ := antichain_dense_l hZFC O hp denseE
  let η : Env M 1 := ⟨fun _ => R,fun _ => R⟩
  let ψ : BinarySchema 1 := { body := entry_m .newest (.bound 1) (.bound 2) }
  have sat a c : ψ.denote η a c ↔ Entry_d M c a R := entry_sat_l M hZFC.1 ..
  obtain ⟨F,fn,values⟩ := ZFC.uniformize_formula_l I hZFC ψ η (X := A) (Y := C) (by
    intro a ha
    obtain ⟨c,hc,r,hr,rc⟩ := maximal a (below a ha)
    have ca := ((member c).mp (bound c hc).1).2 a ha ⟨r,⟨hr.1,hr.2.1,rc⟩,hr.2.2⟩
    exact ⟨c,hc,(sat a c).mpr ca⟩)
  have values a c (ac : Entry_d M a c F) := (sat a c).mp (values a c ac)
  refine ⟨C,F,antiC,(fun c hc => ⟨((member c).mp (bound c hc).1).1,(bound c hc).2⟩),maximal,⟨fn,?_⟩,values⟩
  intro a b c ac bc
  have hc := antiC.1 c (fn.output_mem_of_pairMember ac)
  exact anti.2 a b (fn.input_mem_of_pairMember ac) (fn.input_mem_of_pairMember bc)
    ⟨c,⟨hc.1,hc.2,values a c ac⟩,values b c bc⟩

end YesMetaZFC.Model.Forcing.Internal
