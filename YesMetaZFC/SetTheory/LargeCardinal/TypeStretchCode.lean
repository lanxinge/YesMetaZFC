import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedCode

/-! # 类型伸展的有界矩阵

在低秩传递容器中塌缩全部有界代表，以常值节点读取原类型的像，再按查询域
取交。节点、求值图和像类型都限定在原所属源内，整个矩阵为 Δ₀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Eb_stretch_d (ω κ L K X B F t D v : M.Domain) : Prop :=
  ∃ A, M.mem A X ∧ ∃ Q, M.mem Q X ∧ ∃ Y, M.mem Y X ∧ ∃ e, M.mem e X ∧ ∃ y, M.mem y X ∧
    Eb_collapse_d ω κ L K X B F A Q Y e ∧ Eb_const_d X B A e t y ∧
      ∀ p, M.mem p v ↔ M.mem p D ∧ M.mem p y

def et_stretch0_m {d} (ω κ L K X B F H t D v : Term d) : Formula 1 d := set[d] ⟪
  ∃ A ∈ ⌜X⌝ₛ, ∃ Q ∈ ⌜X⌝ₛ, ∃ Y ∈ ⌜X⌝ₛ, ∃ e ∈ ⌜X⌝ₛ, ∃ y ∈ ⌜X⌝ₛ,
    ⌜eb_collapse_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜K⌝ₛ, ⌜X⌝ₛ, ⌜B⌝ₛ, ⌜F⌝ₛ, A, Q, Y, e, ⌜H⌝ₛ) ∧
    ⌜eb_const_m⌝ₚ(⌜X⌝ₛ, ⌜B⌝ₛ, A, e, ⌜t⌝ₛ, y) ∧
    ⌜v⌝ₛ ⊆ ⌜D⌝ₛ ∧ (∀ p ∈ ⌜D⌝ₛ, p ∈ ⌜v⌝ₛ ↔ p ∈ y)⟫
derive_free_closed et_stretch0_m

theorem et_stretch0_delta_l {d} (ω κ L K X B F H t D v : Term d) :
    (et_stretch0_m ω κ L K X B F H t D v).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (eb_collapse_delta_l ..) (.conj (eb_const_delta_l ..)
      (.conj (.atom ..) (.forallMem _ (.iff (.mem ..) (.mem ..))))))))))

theorem et_stretch0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω κ L K X B F H t D v : Term d)
    (seq : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ) (L.eval ρ) (H.eval ρ)) :
    Formula.satisfies ρ (et_stretch0_m ω κ L K X B F H t D v) ↔
      Eb_stretch_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (X.eval ρ) (B.eval ρ)
        (F.eval ρ) (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
  let w (a : Term d) := a.weaken.weaken.weaken.weaken.weaken
  have collapse (A Q Y e y : M.Domain) :
      Formula.satisfies (((((ρ.push A).push Q).push Y).push e).push y)
        (eb_collapse_m (w ω) (w κ) (w L) (w K) (w X) (w B) (w F)
          Term.newest.weaken.weaken.weaken.weaken Term.newest.weaken.weaken.weaken
          Term.newest.weaken.weaken Term.newest.weaken (w H)) ↔
      Eb_collapse_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (X.eval ρ) (B.eval ρ) (F.eval ρ) A Q Y e := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      eb_collapse_sat_l hKP (((((ρ.push A).push Q).push Y).push e).push y)
        (w ω) (w κ) (w L) (w K) (w X) (w B) (w F)
        Term.newest.weaken.weaken.weaken.weaken Term.newest.weaken.weaken.weaken
        Term.newest.weaken.weaken Term.newest.weaken (w H)
        (by simpa only [w, Definitional.Term.eval_weaken] using seq)
  dsimp only [w] at collapse
  simp only [et_stretch0_m, Eb_stretch_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    collapse, eb_const_sat_l hKP.1, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  refine exists_congr fun A => and_congr_right fun _ => exists_congr fun Q => and_congr_right fun _ =>
    exists_congr fun Y => and_congr_right fun _ => exists_congr fun e => and_congr_right fun _ =>
      exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  exact ⟨fun ⟨sub, all⟩ p => ⟨fun hp => ⟨sub p hp, (all p (sub p hp)).mp hp⟩,
    fun ⟨hp, hy⟩ => (all p hp).mpr hy⟩, fun cut =>
      ⟨fun p hp => ((cut p).mp hp).1, fun p hp => (cut p).trans (and_iff_right hp)⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
