import YesMetaZFC.SetTheory.LargeCardinal.RankLookupSyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSource

/-! # 源内实际的双坐标枚举读取函数

有效索引读枚举值，其余输入取 κ。源内有界统一化给出总图；以下保留有效
索引的精确求值律，供原嵌入直接传输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem er_lookup_l (hZFC : M.Models ZFC) {ω κ K X R T G n D i r : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hT : M.TransitiveSet T)
    (hTX : M.mem T X) (hGX : M.mem G X) (hκT : M.mem κ T) (hG : Fn0_d κ T G)
    (enums : ∀ α p, Rd_entry_d α p G → Er_enum_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) α p)
    (hn : M.mem n ω) (hD : Ep_space_d κ n D) (hi : M.mem i n) (hr : M.mem r n) :
    ∃ f, M.mem f X ∧ Fn0_d D T f ∧
      ∀ s x, M.mem s D → Er_hit_d T G i r s x → Rd_entry_d s x f := by
  let hZF := ZFC.models_zf_l hZFC
  let ρ := ((((⟨fun _ => T, fun _ => T⟩ : Env M 1).push G).push i).push r).push κ
  let φ : BinarySchema 5 := {
    body := .disj (er_hit_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)
      (.conj (Formula.extensionalEq .newest (.bound 2)) (.neg (Formula.existsMem (.bound 6)
        (er_hit_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) .newest)))) }
  have sat s x : φ.denote ρ s x ↔ Er_hit_d T G i r s x ∨ (x = κ ∧ ¬ ∃ y, M.mem y T ∧ Er_hit_d T G i r s y) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, er_hit_sat_l hZF.1,
      Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_existsMem_iff]; rfl
  have hinX a (ha : M.mem a n) := source.transitive ω source.omega_mem a (source.omega.transitive hZF n hn a ha)
  obtain ⟨χ, c, d, H, S, e, hχ, hωχ, hH, hm, ht, he⟩ := source.presentation
  obtain ⟨f, C, hfX, hCX, hf, fs⟩ := smap_uniform_source_l hZFC source.omega hχ hωχ hH source.transitive hm ht he φ
    (.disj (er_hit_delta_l ..) (.conj (.atom _ _ _) (.neg (.existsMem _ (er_hit_delta_l ..))))) ρ
    (Fin.cases source.cardinal_mem (Fin.cases (hinX r hr) (Fin.cases (hinX i hi) (Fin.cases hGX (fun _ => hTX)))))
    (source.space_mem_l hZF hn hD) (fun s _ => by
      classical
      by_cases hit : ∃ x, M.mem x T ∧ Er_hit_d T G i r s x
      · obtain ⟨x, hx, hit⟩ := hit
        exact ⟨x, source.transitive T hTX x hx, (sat s x).mpr (Or.inl hit)⟩
      · exact ⟨κ, source.cardinal_mem, (sat s κ).mpr (Or.inr ⟨rfl, hit⟩)⟩)
  have bound s x (hsx : Rd_entry_d s x f) : M.mem x T :=
    ((sat s x).mp (fs s x hsx)).elim (Er_hit_d.bound_l hT) (fun hh => hh.1.symm ▸ hκT)
  refine ⟨f, hfX, hf.retarget_l bound, fun s x hs hit => ?_⟩
  obtain ⟨y, _, hsy⟩ := hf.2.1 s hs
  rcases (sat s y).mp (fs s y hsy) with hy | ⟨_, impossible⟩
  · exact er_hit_unique_l (ZF.modelsKP hZF) ((hD s).mp hs) hG enums hy hit ▸ hsy
  · exact (impossible ⟨x, hit.bound_l hT, hit⟩).elim

end YesMetaZFC.SetTheory.LargeCardinal
