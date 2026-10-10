import YesMetaZFC.SetTheory.LargeCardinal.TypeStretchBounded
import YesMetaZFC.Model.SetTheory.Internal.FiniteSpaceBounded

/-! # 类型伸展的单一原有界公式

有限列空间和传递容器均由公式内部量化。实际源的有限列闭包识别这些空间，
相对极限秩段提供一个低秩容器，完整等价式读取原来的实际类型伸展。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def et_stretch_m {d} (ω κ L X F t D v : Term d) : Formula 1 d := set[d] ⟪
  ∃ K ∈ ⌜X⌝ₛ, ∃ H ∈ ⌜X⌝ₛ, ∃ B ∈ ⌜X⌝ₛ,
    ⌜fs_space0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜κ⌝ₛ, K) ∧ ⌜fs_space0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜L⌝ₛ, H) ∧
    ⌜Formula.isTransitive⌝ₚ(B) ∧ ⌜t⌝ₛ ∈ B ∧
    ⌜et_stretch0_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, K, ⌜X⌝ₛ, B, ⌜F⌝ₛ, H, ⌜t⌝ₛ, ⌜D⌝ₛ, ⌜v⌝ₛ)⟫
derive_free_closed et_stretch_m

theorem et_stretch_delta_l {d} (ω κ L X F t D v : Term d) : (et_stretch_m ω κ L X F t D v).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (fs_space0_delta_l ..) (.conj (fs_space0_delta_l ..)
    (.conj (Formula.isTransitive_delta0 _) (.conj (.mem ..) (et_stretch0_delta_l ..)))))))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem et_stretch_sat_l {d K₀ R V c c' N S j} (ρ : Env M d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) K₀ (X.eval ρ) R) (power : Sc_power_d (X.eval ρ))
    (family : Em_source_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ))
    (hm : Smem_d I c (X.eval ρ) R) (hn : Smem_d I c' N S)
    (ultra : It_ultra_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) c c' j)
    (hL : M.mem (L.eval ρ) (X.eval ρ)) (hF : M.mem (F.eval ρ) (X.eval ρ))
    (hl : M.IsLimitOrdinal (L.eval ρ)) (level : Er_level_d (X.eval ρ) (L.eval ρ) V)
    (hκ : M.mem (κ.eval ρ) V) (ht : M.mem (t.eval ρ) V) :
    Formula.satisfies ρ (et_stretch_m ω κ L X F t D v) ↔
      Et_stretch_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (X.eval ρ) R (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
  obtain ⟨H₀, hH₀, seq⟩ := source.sequences.space (L.eval ρ) hL
  let w (a : Term d) := a.weaken.weaken.weaken
  have sk (K H B : M.Domain) : Formula.satisfies (((ρ.push K).push H).push B)
      (fs_space0_m (w ω) (w X) (w κ) Term.newest.weaken.weaken) ↔ K = K₀ := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      fs_space0_iff_l (ZF.modelsKP hZF) (K₀ := K₀) (((ρ.push K).push H).push B)
        (w ω) (w X) (w κ) Term.newest.weaken.weaken
        (by simpa only [w, Definitional.Term.eval_weaken] using source.finite)
        (by simpa only [w, Definitional.Term.eval_weaken, Structure.MemberSubset] using source.transitive K₀ source.finite_mem)
  have sl (K H B : M.Domain) : Formula.satisfies (((ρ.push K).push H).push B)
      (fs_space0_m (w ω) (w X) (w L) Term.newest.weaken) ↔ H = H₀ := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      fs_space0_iff_l (ZF.modelsKP hZF) (K₀ := H₀) (((ρ.push K).push H).push B)
        (w ω) (w X) (w L) Term.newest.weaken
        (by simpa only [w, Definitional.Term.eval_weaken] using seq)
        (by simpa only [w, Definitional.Term.eval_weaken, Structure.MemberSubset] using source.transitive H₀ hH₀)
  have core (K B : M.Domain) : Formula.satisfies (((ρ.push K).push H₀).push B)
      (et_stretch0_m (w ω) (w κ) (w L) Term.newest.weaken.weaken (w X) .newest (w F)
        Term.newest.weaken (w t) (w D) (w v)) ↔
      Eb_stretch_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) K (X.eval ρ) B (F.eval ρ) (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      et_stretch0_sat_l (ZF.modelsKP hZF) (((ρ.push K).push H₀).push B)
        (w ω) (w κ) (w L) Term.newest.weaken.weaken (w X) .newest (w F)
        Term.newest.weaken (w t) (w D) (w v)
        (by simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using seq)
  dsimp only [w] at sk sl core
  simp only [et_stretch_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    sk, sl, Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨K, _, H, _, B, hB, eqK, eqH, trans, htB, matrix⟩
    subst K H
    exact ((core K₀ B).mp matrix).read_l hZF source family hm hn ultra hB trans htB
  · intro stretch
    have htX := source.transitive V level.member (t.eval ρ) ht
    obtain ⟨P, hP, pair⟩ := source.theory.algebra.pair (t.eval ρ) (t.eval ρ) htX htX
    have hPV := level.hierarchy.pair_mem_l hZF source.transitive level.member hl ht ht hP pair
    obtain ⟨B, hB, trans, sub⟩ := sc_rank_cover_l hZF source.transitive level.member level.hierarchy P hPV
    have htB := sub (t.eval ρ) ((pair (t.eval ρ)).mpr (Or.inl rfl))
    exact ⟨K₀, source.finite_mem, H₀, hH₀, B, source.transitive V level.member B hB,
      rfl, rfl, trans, htB, (core K₀ B).mpr (stretch.bounded_l hZF source power family hL hF hl level hκ hB trans htB)⟩

end YesMetaZFC.SetTheory.LargeCardinal
