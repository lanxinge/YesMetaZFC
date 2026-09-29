import YesMetaZFC.Model.Forcing.InternalNameConstruction
import YesMetaZFC.Model.Forcing.InternalCheckModel
import YesMetaZFC.SetTheory.Ord.Natural

/-! # 内部名称扩张的配对、并集与无穷

有限配对使用任意被滤子接受的标签；并集同时加强两层成员的系数。
无穷公理解释地模型的归纳集，不预设内部 ω 等于宿主 ω。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)

local notation "E" => extension_l M hZF B R z U
include O hZF hU

theorem internal_pair_l (A C : (E).Domain) : ∃ Q : (E).Domain, ∀ x : (E).Domain,
    x ∈ Q ↔ x = A ∨ x = C := by
  obtain ⟨s, hs, hA⟩ := value_name_l A
  obtain ⟨t, ht, hC⟩ := value_name_l C
  obtain ⟨b, hb⟩ := hU.inhabited
  have hbB := (hU.proper b hb).1
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨q, hq, he⟩ := name_pair_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hs ht hbB hbB
  obtain ⟨Q, hQ⟩ := name_value_l (R := R) (z := z) (U := U) hq
  refine ⟨Q, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨a, c, ⟨p, hp, hpq⟩, _, hav⟩ := (qval_mem_l O hZF hU hQ).mp hx
    rcases (he p).mp hpq with hps | hpt
    · obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hps
      exact Or.inl (qval_unique_l hav hA)
    · obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hpt
      exact Or.inr (qval_unique_l hav hC)
  · rintro (rfl | rfl)
    · obtain ⟨p, hp⟩ := I.total s b
      exact (qval_mem_l O hZF hU hQ).mpr ⟨s, b, ⟨p, hp, (he p).mpr (Or.inl hp)⟩, hb, hA⟩
    · obtain ⟨p, hp⟩ := I.total t b
      exact (qval_mem_l O hZF hU hQ).mpr ⟨t, b, ⟨p, hp, (he p).mpr (Or.inr hp)⟩, hb, hC⟩

theorem internal_union_l (A : (E).Domain) : ∃ Q : (E).Domain, ∀ x : (E).Domain,
    x ∈ Q ↔ ∃ y : (E).Domain, y ∈ A ∧ x ∈ y := by
  obtain ⟨t, ht, hA⟩ := value_name_l A
  obtain ⟨S, htS, hS⟩ := ht
  let δ : Env M 2 := (⟨fun _ => t, fun _ => t⟩ : Env M 1).push R
  let φ : BinarySchema 2 := {
    body := .existsE (.conj (source_m (.bound 3) (.bound 4) .newest (.bound 1))
      (source_m (.bound 3) .newest (.bound 2) (.bound 1))) }
  have hφ s p : φ.denote δ s p ↔ ∃ a, Source_d M R t a p ∧ Source_d M R a s p := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      source_sat_l M hZF.1]
    rfl
  obtain ⟨q, hq, _, he⟩ := name_comp_l M hZF φ δ B S (fun a ha => ⟨S, ha, hS⟩)
  obtain ⟨Q, hQ⟩ := name_value_l (R := R) (z := z) (U := U) hq
  refine ⟨Q, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨s, p, hs, hp, hsv⟩ := (qval_mem_l O hZF hU hQ).mp hx
    obtain ⟨a, ha, has⟩ := (hφ s p).mp ((he s p).mp hs).2.2
    have han : Name_d M B a := ha.elim fun c hc => (name_entry_l M ⟨S, htS, hS⟩ hc.1).1
    obtain ⟨y, hay⟩ := name_value_l (R := R) (z := z) (U := U) han
    exact ⟨y, source_val_l O hZF hU hA hay ha hp, source_val_l O hZF hU hay hsv has hp⟩
  · rintro ⟨y, hy, hx⟩
    obtain ⟨a, c, ha, hc, hav⟩ := (qval_mem_l O hZF hU hA).mp hy
    obtain ⟨s, d, hs, hd, hsv⟩ := (qval_mem_l O hZF hU hav).mp hx
    obtain ⟨p, hp, hpc, hpd⟩ := hU.directed c d hc hd
    have hsS := (supp_entry_l M hS (supp_entry_l M hS htS ha).1 hs).1
    exact (qval_mem_l O hZF hU hQ).mpr ⟨s, p, (he s p).mpr
      ⟨hsS, (hU.proper p hp).1, (hφ s p).mpr ⟨a, ⟨c, ha, hpc⟩, ⟨d, hs, hpd⟩⟩⟩, hp, hsv⟩

theorem check_val_mem_l {b a t} {x y : Name_quot_l M B R z U}
    (hc : Check_d M b a t) (hv : Qval_d M B R z U t x) (hb : U b) :
    y ∈ x ↔ ∃ c s, M.mem c a ∧ Check_d M b c s ∧ Qval_d M B R z U s y := by
  constructor
  · intro hy
    obtain ⟨s, p, hs, _, hsy⟩ := (qval_mem_l O hZF hU hv).mp hy
    obtain ⟨_, c, hca, hcs⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) hc s p).mp hs
    exact ⟨c, s, hca, hcs, hsy⟩
  · rintro ⟨c, s, hca, hcs, hsy⟩
    exact (qval_mem_l O hZF hU hv).mpr ⟨s, b, (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) hc s b).mpr ⟨rfl, c, hca, hcs⟩, hb, hsy⟩

theorem internal_infinity_l : ∃ W : (E).Domain,
    (∃ e : (E).Domain, (∀ x : (E).Domain, ¬ x ∈ e) ∧ e ∈ W) ∧
    ∀ x : (E).Domain, x ∈ W → ∃ s : (E).Domain,
      (∀ y : (E).Domain, y ∈ s ↔ y ∈ x ∨ y = x) ∧ s ∈ W := by
  obtain ⟨b, hb⟩ := hU.inhabited
  have cv a : ∃ t, ∃ x : (E).Domain, Check_d M b a t ∧ Qval_d M B R z U t x := by
    obtain ⟨t, ht, hn, _⟩ := zf_check_l M hZF (hU.proper b hb).1 a
    obtain ⟨x, hx⟩ := name_value_l (R := R) (z := z) (U := U) hn
    exact ⟨t, x, ht, hx⟩
  obtain ⟨I, ⟨e, he, hei⟩, hI⟩ := KP.exists_inductive (ZF.modelsKP hZF)
  obtain ⟨tI, W, hcI, hvI⟩ := cv I
  obtain ⟨te, E', hce, hve⟩ := cv e
  refine ⟨W, ⟨E', fun x hx => ?_, ?_⟩, fun x hx => ?_⟩
  · obtain ⟨c, _, hc, _⟩ := (check_val_mem_l O hZF hU hce hve hb).mp hx
    exact he c hc
  · exact (check_val_mem_l O hZF hU hcI hvI hb).mpr ⟨e, te, hei, hce, hve⟩
  · obtain ⟨a, ta, hai, hca, hva⟩ := (check_val_mem_l O hZF hU hcI hvI hb).mp hx
    obtain ⟨s, hsa, hsi⟩ := hI a hai
    obtain ⟨ts, S, hcs, hvs⟩ := cv s
    refine ⟨S, fun y => ?_, (check_val_mem_l O hZF hU hcI hvI hb).mpr ⟨s, ts, hsi, hcs, hvs⟩⟩
    constructor
    · intro hy
      obtain ⟨c, tc, hct, hcc, hvc⟩ := (check_val_mem_l O hZF hU hcs hvs hb).mp hy
      rcases (hsa c).mp hct with hca' | hEq
      · exact Or.inl ((check_val_mem_l O hZF hU hca hva hb).mpr ⟨c, tc, hca', hcc, hvc⟩)
      · have heq := hZF.1.eq_of_same_members c a hEq
        subst c
        have ht := check_unique_l M hZF.1 (check_ind_l M hZF) b a tc ta hcc hca
        exact Or.inr (qval_unique_l (ht ▸ hvc) hva)
    · rintro (hy | rfl)
      · obtain ⟨c, tc, hca', hcc, hvc⟩ := (check_val_mem_l O hZF hU hca hva hb).mp hy
        exact (check_val_mem_l O hZF hU hcs hvs hb).mpr ⟨c, tc, (hsa c).mpr (Or.inl hca'), hcc, hvc⟩
      · exact (check_val_mem_l O hZF hU hcs hvs hb).mpr ⟨a, ta, hsa.predecessor_mem, hca, hva⟩

end YesMetaZFC.Model.Forcing.Internal
