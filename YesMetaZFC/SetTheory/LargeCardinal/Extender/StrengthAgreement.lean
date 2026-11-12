import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawExactHistory
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SetCode

/-! # 从序数子集覆盖得到支撑以下的有限幂一致性

先在目标中编号有限幂，再把该编号沿已有的反向一致性送回源。源子集的
编号像是一个较小序数的子集；强度覆盖搬运此像，原单射随后恢复同一个子集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 一项序列空间的坐标恰好回收字母表；目标源不必预先拥有 κ。 -/
theorem Ea_subset_d.alphabet_l {ω κ K X R μ J Y S : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ J Y S) (ho : M.IsOrdinal κ) : ∃ K', Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S := by
  obtain ⟨z, _, hz⟩ := source.omega.1.1
  obtain ⟨o, os, hot⟩ := source.omega.1.2 z hz
  obtain ⟨D, hD, ds⟩ := source.space_l hZF hot
  have hDY := subsets o D D hot ds (fun _ h => h) hD
  obtain ⟨U, hU, us⟩ := (target.algebra_l (ZF.modelsKP hZF)).union D hDY
  obtain ⟨C, hC, coords⟩ := (target.algebra_l (ZF.modelsKP hZF)).envelope_l hU
  obtain ⟨c, hc⟩ := target.code
  let ρ : Env M 2 := ⟨Fin.cases U (fun _ => ω), fun _ => U⟩
  let φ : UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3) (kpair0_m (.bound 1) .newest (.bound 2))) }
  have sat a : φ.denote ρ a ↔ ∃ p, M.mem p U ∧ ∃ i, M.mem i ω ∧ KPair_d M p i a := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  obtain ⟨A, hA, spec⟩ := sc_separate_source_l I hZF target.omega target.transitive hc target.theory φ
    (.existsMem _ (.existsMem _ (kpair0_delta_l ..))) ρ (Fin.cases hU (fun _ => target.omega_mem)) hC
  have eq : A = κ := hZF.1.eq_of_same_members A κ (fun a => by
    rw [spec a, sat a]
    constructor
    · rintro ⟨_, p, hp, i, _, pair⟩
      obtain ⟨f, hf, hpf⟩ := (us p).mp hp
      exact (((ds f).mp hf).bound_l ⟨p, pair, hpf⟩).2
    · intro ha
      obtain ⟨f, fn, values⟩ := ZF.exists_constantFunction hZF I (source := o) ha
      obtain ⟨p, pair, hpf⟩ := (values z a).mpr ⟨os.predecessor_mem, rfl⟩
      have hp := (us p).mpr ⟨f, (ds f).mpr (fn0_of_function_l (ZF.modelsKP hZF) fn), hpf⟩
      exact ⟨(coords z a ⟨p, pair, hp⟩).2, p, hp, z, hz, pair⟩)
  have hκY := eq ▸ hA
  exact target.rebase_l hκY source.below
    (sc_ordinal_small_l hZF target.omega target.transitive hc target.theory hκY ho)

theorem Ea_subset_d.set_l {ω κ K X R K' Y S A : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S) (hA : M.mem A X) (sub : M.MemberSubset A κ) : M.mem A Y := by
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨d, hd⟩ := target.code
  obtain ⟨z, _, hz⟩ := source.omega.1.1
  obtain ⟨f, C, hf, _, fn, values⟩ := sc_constant_l hZF source.omega source.transitive hc source.theory hA
    (source.transitive ω source.omega_mem z hz)
  have hfY := subsets.relation_l hZF source target hf (fun p hp => by
    obtain ⟨a, ha, b, _, pair⟩ := fn.1 p hp
    exact ⟨a, sub a ha, b, ((values a b).mp ⟨p, pair, hp⟩).2.symm ▸ source.below z hz, pair⟩)
  exact sc_function_domain_mem_l hZF target.omega target.transitive hd target.theory hfY fn

/-- 目标中的实际有限幂编号与反向包含把序数子集覆盖升级为有限幂覆盖。 -/
theorem ea_subset_cover_l {ω κ K X R K' Y S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S) (ho : M.IsOrdinal κ)
    (cover : ∀ A, M.mem A X → M.MemberSubset A κ → M.mem A Y)
    (back : Ea_subset_d ω κ Y X) : Ea_subset_d ω κ X Y := by
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨d, hd⟩ := target.code
  intro n D A hn space sub hA
  have hD := target.space_mem_l hZF hn space
  obtain ⟨e, he, ei⟩ := target.finite_index_l hZF ho
  have index := (Sc_index_d.of_injection_l (ZF.modelsKP hZF) ho ei).mono_l
    (fun f hf => ((target.finite_l (ZF.modelsKP hZF)) f).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ((space f).mp hf)⟩)
  obtain ⟨g, hg, gi⟩ := index.restrict_l hZF target.omega target.transitive hd target.theory hD target.cardinal_mem he
  have hgX := back.function_l hZF target source hn space hg (fn0_of_function_l (ZF.modelsKP hZF) gi.1)
  let ρ : Env M 2 := ⟨Fin.cases g (fun _ => A), fun _ => A⟩
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (rd_entry0_m .newest (.bound 1) (.bound 2)) }
  have read y : φ.denote ρ y ↔ ∃ a, M.mem a A ∧ Rd_entry_d a y g := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨C, hC, cs⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (rd_entry0_delta_l ..)) ρ (Fin.cases hgX (fun _ => hA)) source.cardinal_mem
  have hCY := cover C hC (fun y hy => ((cs y).mp hy).1)
  let η : Env M 2 := ⟨Fin.cases g (fun _ => C), fun _ => C⟩
  let ψ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (rd_entry0_m (.bound 1) .newest (.bound 2)) }
  have decode a : ψ.denote η a ↔ ∃ y, M.mem y C ∧ Rd_entry_d a y g := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨B, hB, bs⟩ := sc_separate_source_l I hZF target.omega target.transitive hd target.theory ψ
    (.existsMem _ (rd_entry0_delta_l ..)) η (Fin.cases hg (fun _ => hCY)) hD
  have eq := hZF.1.eq_of_same_members B A (fun a => by
    rw [bs a, decode a]
    constructor
    · rintro ⟨_, y, hy, hay⟩
      obtain ⟨b, hb, hby⟩ := (read y).mp ((cs y).mp hy).2
      exact gi.2 b a y hby hay ▸ hb
    · intro ha
      obtain ⟨y, hy, hay⟩ := gi.1.2.2 a (sub a ha)
      exact ⟨sub a ha, y, (cs y).mpr ⟨hy, (read y).mpr ⟨a, ha, hay⟩⟩, hay⟩)
  exact eq ▸ hB

theorem Es_strength_d.agree_l {ω L K X R K' Y S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω L K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω L K' Y S)
    (ho : M.IsOrdinal L) (hωL : M.mem ω L) (back : Ea_subset_d ω L Y X)
    (strength : Es_strength_d X L Y) : ∀ μ, M.mem μ L → Ea_agree_d ω μ X Y := by
  obtain ⟨c, mx⟩ := source.code
  obtain ⟨d, my⟩ := target.code
  have forward ν (hν : M.mem ν L) (hw : M.MemberSubset ω ν) : Ea_subset_d ω ν X Y := by
    have sub := ho.transitive ν hν
    obtain ⟨K₀, sx⟩ := source.rebase_l (source.transitive L source.cardinal_mem ν hν) hw (source.cardinal_small.mono_mem_l I mx (source.transitive L source.cardinal_mem ν hν) sub)
    obtain ⟨K₁, sy⟩ := target.rebase_l (target.transitive L target.cardinal_mem ν hν) hw (target.cardinal_small.mono_mem_l I my (target.transitive L target.cardinal_mem ν hν) sub)
    exact ea_subset_cover_l hZF sx sy (ho.mem hν) (fun A hA => strength.1 ν hν A hA) (back.mono_l hZF sub)
  intro μ hμ
  have up : Ea_subset_d ω μ X Y := by
    rcases (ho.mem hμ).trichotomy hZF.1 (source.omega.isOrdinal (ZF.modelsKP hZF)) (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) μ ω) with eq | lt | gt
    · exact (hZF.1.eq_of_same_members μ ω eq).symm ▸ forward ω hωL (fun _ h => h)
    · exact (forward ω hωL (fun _ h => h)).mono_l hZF (source.omega.transitive (ZF.modelsKP hZF) μ lt)
    · exact forward μ hμ ((ho.mem hμ).transitive ω gt)
  exact fun n D A hn hd sub => ⟨up n D A hn hd sub, (back.mono_l hZF (ho.transitive μ hμ)) n D A hn hd sub⟩

end YesMetaZFC.SetTheory.LargeCardinal
