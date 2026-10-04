import YesMetaZFC.Model.SetTheory.Internal.UniversalClosure
import YesMetaZFC.Model.SetTheory.Internal.Uniformization

/-! # 源模型实际满足的全内部分离与统一化模式

模式量化全部内部公式码和赋值。正则 Hχ 给出真实实例；后继模型的保持
由全称闭包证明，因而覆盖新模型中不在旧嵌入像内的参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Sc_theory_d (ω X R : M.Domain) : Prop where
  separation : ∀ E F n r i f D, M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
    M.mem i ω → M.mem f E → M.mem D X → ∃ A, M.mem A X ∧ Ssep_d I X R E F n r i f D A
  uniformization : ∀ E F n r i j f D, M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
    M.mem i ω → M.mem j ω → i ≠ j → M.mem f E → M.mem D X → Scollect_d I X R E F n r i j f D X →
      ∃ B C, M.mem B X ∧ M.mem C X ∧ Suniform_d I X R E F n r i j f D C B

theorem sc_h_theory_l (hZFC : M.Models ZFC) {ω χ H : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H) (R : M.Domain) :
    Sc_theory_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω H R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨fun E F n r i f D _ _ _ _ _ hD => ?_, fun E F n r i j f D _ _ _ _ _ _ _ hD ht => ?_⟩
  · obtain ⟨A, hA⟩ := ssep_exists_l I hZF H R E F n r i f D
    exact ⟨A, ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH hD A (fun x hx => ((hA x).mp hx).1), hA⟩
  · exact h_uniform_l hZFC hω hχ hωχ hH hD ht

theorem sc_source_theory_l (hZFC : M.Models ZFC) {ω χ c d X R H S q : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d H S)
    (hq : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d X H q) :
    Sc_theory_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨fun E F n r i f D hE hF hr hi hf hD => ?_, fun E F n r i j f D hE hF hr hi hj hij hf hD hh => ?_⟩
  · obtain ⟨D', hD', hDD⟩ := hq.1.1.2.2 D hD
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D'
    exact smap_separation_l I hZF hω hX (ZF.h_transitive_l I hZF hH) hm hn hq hP
      (fun A hA => ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH hD' A ((hP A).mp hA)) hE hF hr hi hf hDD
  · exact smap_uniform_l hZFC hω hχ hωχ hH hX hm hn hq hE hF hr hi hj hij hf hD hh

theorem sc_separation_forward_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (source : Sc_theory_d I ω X R) {K F n r i g D : M.Domain}
    (hK : M.IsFunctionSpace I K ω Y) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hg : M.mem g K) (hD : M.mem D Y) : ∃ A, M.mem A Y ∧ Ssep_d I Y S K F n r i g D A := by
  obtain ⟨b, s, t, hb, hs, ht, hsi, hti, _, _, hst, hsb, htb⟩ := sbound_fresh_l I hZF hω hF hi hi
  obtain ⟨m, G, k, build, code⟩ := sfm_sep_l I hZF hω hF hr hi hs ht hsi hti hst hb htb
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  -- 源中的分离模式先变成对全部赋值有效的单一内部程序。
  have valid f (hf : M.mem f E) : Ssat_d I X R E G m k f := by
    obtain ⟨D, hD, hsD⟩ := ((hE f).mp hf).2.2 s hs
    exact (code X R E c f D hX hm hE hf hsD).mpr (source.separation E F n r i f D hE hF hr hi hf hD)
  obtain ⟨g', update, hgf⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs hD
  obtain ⟨A, hAY, hA⟩ := (code Y S K d g' D hY hn hK ((hK g').mpr hgf)
    ((update.2 s D).mpr (Or.inl ⟨rfl, rfl⟩))).mp
    ((hq.valid_l I hZF hω hm.1 hn.1 build.program build.root hE hK).mp valid g' ((hK g').mpr hgf))
  exact ⟨A, hAY, (ssep_agree_l I hZF hF hb hr hi hK hg ((hK g').mpr hgf)
    (update.agree_l I hsb) (hY D hD)).mpr hA⟩

theorem sc_uniform_forward_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (source : Sc_theory_d I ω X R) {K F n r i j g D : M.Domain}
    (hK : M.IsFunctionSpace I K ω Y) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hg : M.mem g K) (hD : M.mem D Y)
    (total : Scollect_d I Y S K F n r i j g D Y) :
    ∃ B C, M.mem B Y ∧ M.mem C Y ∧ Suniform_d I Y S K F n r i j g D C B := by
  obtain ⟨s, hs, hb, his, hjs⟩ := sbound_above_l I hZF hω hF hi hj
  obtain ⟨t, ht, htω⟩ := hω.1.2 s hs
  obtain ⟨u, hu, huω⟩ := hω.1.2 t htω
  obtain ⟨σ, hσ, hσω⟩ := hω.1.2 u huω
  have st : M.MemberSubset s t := fun x hx => (ht x).mpr (Or.inl hx)
  have tu : M.MemberSubset t u := fun x hx => (hu x).mpr (Or.inl hx)
  have uσ : M.MemberSubset u σ := fun x hx => (hσ x).mpr (Or.inl hx)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hsi : s ≠ i := fun e => ir i (e ▸ his)
  obtain ⟨n₁, F₁, r₁, h₁, uniform⟩ := sfm_uniform_l I hZF hω hF hr hσω
    (uσ i (tu i (st i his))) (uσ j (tu j (st j hjs))) (uσ s (tu s ht.predecessor_mem))
    (uσ t hu.predecessor_mem) hσ.predecessor_mem hij hsi (fun e => ir i (e ▸ st i his))
    (fun e => ir j (e ▸ st j hjs)) (fun e => ir t (e ▸ ht.predecessor_mem))
    (fun e => ir s (e ▸ tu s ht.predecessor_mem)) (fun e => ir t (e ▸ hu.predecessor_mem)) hb (fun h => ir t (st t h))
  obtain ⟨n₂, F₂, r₂, h₂, antecedent⟩ := sfm_total_l I hZF hω h₁.program (h₁.span r hr) hi hj hs hsi
  -- 传输的是“逐点存在 ⇒ 统一函数存在”，因此适用于目标中的新集合与新参数。
  obtain ⟨m, G, k, build, implication⟩ := sfm_imp_l I hZF hω h₂.program h₂.root (h₂.span r₁ h₁.root)
  have initial Z U E f A C : Scollect_d I Z U E F₁ n₁ r i j f A C ↔ Scollect_d I Z U E F n r i j f A C :=
    forall_congr' fun x => imp_congr_right fun _ => exists_congr fun y => and_congr_right fun _ =>
      exists_congr fun v => exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ =>
        (h₁.sat_l I hZF hF hr Z U E w).symm
  have read Z U E e f A (hZ : M.TransitiveSet Z) (he : Smem_d I e Z U)
      (hE : M.IsFunctionSpace I E ω Z) (hf : M.mem f E) (hA : M.PairMember I s A f) :
      Ssat_d I Z U E G m k f ↔ (Scollect_d I Z U E F n r i j f A Z →
        ∃ B C, M.mem B Z ∧ M.mem C Z ∧ Suniform_d I Z U E F n r i j f A C B) := by
    rw [implication Z U E f hf, antecedent Z U E e f A hZ he hE hf hA,
      ← h₂.sat_l I hZF h₁.program h₁.root Z U E f, uniform Z U E e f A hZ he hE hf hA]
    exact imp_congr (initial Z U E f A Z) Iff.rfl
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  have valid f (hf : M.mem f E) : Ssat_d I X R E G m k f := by
    obtain ⟨A, hA, hsA⟩ := ((hE f).mp hf).2.2 s hs
    exact (read X R E c f A hX hm hE hf hsA).mpr
      (source.uniformization E F n r i j f A hE hF hr hi hj hij hf hA)
  obtain ⟨g', update, hgf⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs hD
  have agree := update.agree_l I (ir s)
  have total' := (scollect_agree_l I hZF hF hb hr hi hj hK hg ((hK g').mpr hgf) agree
    (hY D hD) (fun _ h => h)).mp total
  obtain ⟨B, C, hB, hC, hf, select⟩ := (read Y S K d g' D hY hn hK ((hK g').mpr hgf)
    ((update.2 s D).mpr (Or.inl ⟨rfl, rfl⟩))).mp
      ((hq.valid_l I hZF hω hm.1 hn.1 build.program build.root hE hK).mp valid g' ((hK g').mpr hgf)) total'
  exact ⟨B, C, hB, hC, hf, fun x y hxy => (sbin_agree_l I hZF hF hb hr hi hj hK hg ((hK g').mpr hgf)
    agree (hY D hD x (hf.bound_l hxy).1) (hY C hC y (hf.bound_l hxy).2)).mpr (select x y hxy)⟩

/-- 理论保持覆盖后继模型的全部参数，不要求它们具有旧参数原像。 -/
theorem Sc_theory_d.map_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (source : Sc_theory_d I ω X R) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q) : Sc_theory_d I ω Y S :=
  ⟨fun _ _ _ _ _ _ _ => sc_separation_forward_l I hZF hω hX hY hm hn hq source,
    fun _ _ _ _ _ _ _ _ => sc_uniform_forward_l I hZF hω hX hY hm hn hq source⟩

end YesMetaZFC.SetTheory.Internal
