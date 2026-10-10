import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptShift
import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptLift
import YesMetaZFC.Model.SetTheory.Internal.RegularRankImage

/-! # 移位秩值的原图定义

秩值是在复制根图的像中，对末结点嵌入唯一确定的联合节点求值。
所有见证均取自已构造的复制历史，定义不另加可延伸性或下降假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Jr_value_d (H G' T G U o F i δ : M.Domain) : Prop := ∃ X A π z Z α g F' P s,
  Ic_at_d H i X A π z Z α ∧ It_map_d G' o i g ∧ Rd_entry_d F F' g ∧
    Ja_lift_d I T G U i π P ∧ KPair_d M s i P ∧ Rd_entry_d s δ F'

def jr_value_m {d} (H G' T G U o F i δ : Term d) : Formula 1 d := set[d] ⟪
  ∃ X A π z Z α g F' P s, ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, ⌜i⌝ₛ, X, A, π, z, Z, α) ∧
    ⌜it_map_m⌝ₚ(⌜G'⌝ₛ, ⌜o⌝ₛ, ⌜i⌝ₛ, g) ∧ ⌜rd_entry0_m⌝ₚ(⌜F⌝ₛ, F', g) ∧
    ⌜ja_lift_m⌝ₚ(⌜T⌝ₛ, ⌜G⌝ₛ, ⌜U⌝ₛ, ⌜i⌝ₛ, π, P) ∧
    ⌜kpair0_m⌝ₚ(s, ⌜i⌝ₛ, P) ∧ ⌜rd_entry0_m⌝ₚ(s, ⌜δ⌝ₛ, F')⟫
derive_free_closed jr_value_m

theorem jr_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H G' T G U o F i δ : Term d) :
    Formula.satisfies ρ (jr_value_m H G' T G U o F i δ) ↔
      Jr_value_d I (H.eval ρ) (G'.eval ρ) (T.eval ρ) (G.eval ρ) (U.eval ρ) (o.eval ρ) (F.eval ρ) (i.eval ρ) (δ.eval ρ) := by
  simp only [jr_value_m, Jr_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ic_at_sat_l hE, it_map_sat_l hE, rd_entry0_sat_l hE, ja_lift_sat_l I hE,
    kpair0_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.embedding_l {ω T Q G E L H Q' G' i X A π z Z α k Y B σ v V β g : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G') (left : Ic_at_d H i X A π z Z α)
    (right : Ic_at_d H k Y B σ v V β) (edge : It_map_d G' i k g) :
    ∃ R S K K', Smem_d J z Z R ∧ Smem_d J v V S ∧ Ep_source_d hZF ω ω K Z R ∧
      Ep_source_d hZF ω ω K' V S ∧ Smap_d J ω z v Z V g := by
  obtain ⟨c, _, hz, row⟩ := hist.row_l hZF left
  obtain ⟨d, _, hv, row'⟩ := hist.row_l hZF right
  obtain ⟨_, _, R, _, _, _, K, _, _, mz, _, _, source, _⟩ := row
  obtain ⟨_, _, S, _, _, _, K', _, _, mv, _, _, target, _⟩ := row'
  exact ⟨R, S, K, K', mz, mv, source.source, target.source,
    hist.diagram.elementary i k g z Z R v V S edge hz hv mz.1 mv.1⟩

end YesMetaZFC.SetTheory.LargeCardinal
