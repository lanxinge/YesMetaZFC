import YesMetaZFC.Model.SetTheory.Internal.UniversalClosure
import YesMetaZFC.Model.SetTheory.Internal.Uniformization
import YesMetaZFC.Model.SetTheory.Internal.SourceSmall
import YesMetaZFC.SetTheory.CumulativeFunction

/-! # 小定义域上的全内部统一化

仅在源内单射可控制的定义域上收集见证。正则 Hχ 与正则极限 Vδ
分别由遗传大小闭包和共尾度秩界给出实例；不要求强极限。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sc_uniform_d (ω X R D : M.Domain) : Prop :=
  ∀ E F n r i j f A, M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
    M.mem i ω → M.mem j ω → i ≠ j → M.mem f E → M.mem A X → M.MemberSubset A D →
    Scollect_d I X R E F n r i j f A X →
      ∃ B C, M.mem B X ∧ M.mem C X ∧ Suniform_d I X R E F n r i j f A C B

def Sc_collection_d (ω X R : M.Domain) : Prop :=
  ∀ D, M.mem D X → Sc_small_d X D → Sc_uniform_d I ω X R D

section Pull
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smap_uniform_l {ω c d X R H S q E F n r i j f D} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hHt : M.TransitiveSet H)
    (hm : Smem_d I c X R) (hn : Smem_d I d H S) (hq : Smap_d I ω c d X H q)
    (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hf : M.mem f E) (hD : M.mem D X)
    (small : Sc_small_d X D) (target : Sc_collection_d I ω H S)
    (hh : Scollect_d I X R E F n r i j f D X) :
    ∃ B C, M.mem B X ∧ M.mem C X ∧ Suniform_d I X R E F n r i j f D C B := by
  obtain ⟨s, hs, hb, his, hjs⟩ := sbound_above_l I hZF hω hF hi hj
  obtain ⟨t, ht, htω⟩ := hω.1.2 s hs
  obtain ⟨u, hu, huω⟩ := hω.1.2 t htω
  obtain ⟨σ, hσ, hσω⟩ := hω.1.2 u huω
  have st : M.MemberSubset s t := fun x hx => (ht x).mpr (Or.inl hx)
  have tu : M.MemberSubset t u := fun x hx => (hu x).mpr (Or.inl hx)
  have uσ : M.MemberSubset u σ := fun x hx => (hσ x).mpr (Or.inl hx)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hsi : s ≠ i := fun e => ir i (e ▸ his)
  obtain ⟨n₁, F₁, r₁, h₁, total⟩ := sfm_total_l I hZF hω hF hr hi hj hs hsi
  obtain ⟨n₂, F₂, r₂, h₂, uniform⟩ := sfm_uniform_l I hZF hω hF hr hσω
    (uσ i (tu i (st i his))) (uσ j (tu j (st j hjs))) (uσ s (tu s ht.predecessor_mem))
    (uσ t hu.predecessor_mem) hσ.predecessor_mem hij hsi (fun e => ir i (e ▸ st i his))
    (fun e => ir j (e ▸ st j hjs)) (fun e => ir t (e ▸ ht.predecessor_mem))
    (fun e => ir s (e ▸ tu s ht.predecessor_mem)) (fun e => ir t (e ▸ hu.predecessor_mem)) hb (fun h => ir t (st t h))
  obtain ⟨f', hv, hfv⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hs hD
  have hf' := (hE f').mpr hfv
  have hsD := (hv.2 s D).mpr (Or.inl ⟨rfl, rfl⟩)
  have agree := hv.agree_l I (ir s)
  have source := (total X R E c f' D hX hm hE hf' hsD).mpr
    ((scollect_agree_l I hZF hF hb hr hi hj hE hf hf' agree (hX D hD) (fun _ h => h)).mp hh)
  obtain ⟨g, hg, hfg⟩ := smap_assign_exists_l I hZF hq.1.1 hfv
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω H
  obtain ⟨D', hDH, hDD⟩ := hq.1.1.2.2 D hD
  have hsD' := hfg s hs D D' hsD hDD
  have image := (hq.ssat_l I hZF.1 hm.1 hn.1 h₁.program h₁.root hE hK hf' ((hK g).mpr hg) hfg).mp source
  obtain ⟨B, C, hBH, hCH, hu⟩ := target D' hDH
    ((hq.small_l hZF hω hX hHt hm hn hDD).mp small) K F n r i j g D'
    hK hF hr hi hj hij ((hK g).mpr hg) hDH (fun _ h => h)
    ((total H S K d g D' hHt hn hK ((hK g).mpr hg) hsD').mp image)
  have image := (uniform H S K d g D' hHt hn hK ((hK g).mpr hg) hsD').mpr ⟨B, C, hBH, hCH, hu⟩
  have source := (hq.ssat_l I hZF.1 hm.1 hn.1 h₂.program h₂.root hE hK hf' ((hK g).mpr hg) hfg).mpr image
  obtain ⟨B, C, hBX, hCX, hBC, select⟩ := (uniform X R E c f' D hX hm hE hf' hsD).mp source
  exact ⟨B, C, hBX, hCX, hBC, fun x y hxy =>
    (sbin_agree_l I hZF hF hb hr hi hj hE hf hf' agree (hX D hD x (hBC.bound_l hxy).1)
      (hX C hCX y (hBC.bound_l hxy).2)).mpr (select x y hxy)⟩

/-- 小定义域的源内编号随图传输，目标统一函数的存在性再回拉。 -/
theorem Sc_collection_d.pull_l {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (h : Sc_collection_d I ω Y S) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q) : Sc_collection_d I ω X R := by
  intro D _ small E F n r i j f A hE hF hr hi hj hij hf hA hAD total
  exact smap_uniform_l hZF hω hX hY hm hn hq hE hF hr hi hj hij hf hA (small.mono_l hAD) h total
end Pull


theorem sc_h_collection_l (hZFC : M.Models ZFC) {ω χ H : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H) (R : M.Domain) :
    Sc_collection_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω H R :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA _ => h_uniform_l hZFC hω hχ hωχ hH hA

theorem sc_v_collection_l (hZFC : M.Models ZFC) {δ V : M.Domain}
    (hδ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ V) (ω R : M.Domain) :
    Sc_collection_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω V R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro D _ small E F n r i j f A _ _ _ _ _ _ _ hA hAD total
  obtain ⟨μ, e, hμ, _, index⟩ := small.mono_l hAD
  let ρ : Env M 9 := ⟨Fin.cases f (Fin.cases j (Fin.cases i (Fin.cases r (Fin.cases n
    (Fin.cases F (Fin.cases E (Fin.cases R (fun _ => V)))))))), fun _ => V⟩
  let φ : BinarySchema 9 := {
    body := sbin_m (𝒞 := kpair_convention_l) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat x y : φ.denote ρ x y ↔ Sbin_d I V R E F n r i j f x y := sbin_sat_l I hZF.1 ..
  obtain ⟨q, hq, select⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := A) (Y := V)
    (fun x hx => (total x hx).imp fun y hy => ⟨hy.1, (sat x y).mpr hy.2⟩)
  obtain ⟨C, hC, hf, hqV⟩ := ZF.v_small_function_l hZF hδ
    (ZF.v_ordinal_height_l hZF hV index.ordinal hμ) (index.bound_l (ZF.modelsKP hZF)) hA hV hq
  exact ⟨q, C, hqV, hC, fn0_of_function_l (ZF.modelsKP hZF) hf, fun x y hxy => (sat x y).mp (select x y hxy)⟩

theorem sc_collection_forward_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (source : Sc_collection_d I ω X R) {K F n r i j g D : M.Domain}
    (hK : M.IsFunctionSpace I K ω Y) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hg : M.mem g K) (hD : M.mem D Y)
    (small : Sc_small_d Y D) (total : Scollect_d I Y S K F n r i j g D Y) :
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
  -- 大小界与单射图占用新槽位，小性守卫和原收集蕴含编入同一程序。
  obtain ⟨τ, hτ, hτω⟩ := hω.1.2 σ hσω
  obtain ⟨ν, hν, hνω⟩ := hω.1.2 τ hτω
  let v : Fin 3 → M.Domain := Fin.cases σ (Fin.cases s (fun _ => τ))
  have vs : ∀ a, M.mem (v a) ν := Fin.cases ((hν σ).mpr (Or.inl hτ.predecessor_mem))
    (Fin.cases ((hν s).mpr (Or.inl ((hτ s).mpr (Or.inl (uσ s (tu s ht.predecessor_mem))))))
      (fun _ => hν.predecessor_mem))
  obtain ⟨n₃, F₃, r₃, h₃, index⟩ := sfm_delta_l I hZF hω build.program
    (sc_index_m .newest (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs)
    (sc_index_delta_l ..) v hνω vs
  obtain ⟨n₄, F₄, r₄, h₄, guarded⟩ := sfm_imp_l I hZF hω h₃.program h₃.root (h₃.span k build.root)
  have read' Z U E e f A μ q (hZ : M.TransitiveSet Z) (he : Smem_d I e Z U)
      (hE : M.IsFunctionSpace I E ω Z) (hf : M.mem f E)
      (hA : M.PairMember I s A f) (hμ : M.PairMember I σ μ f) (hq : M.PairMember I τ q f) :
      Ssat_d I Z U E F₄ n₄ r₄ f ↔ (Sc_index_d μ A q → Scollect_d I Z U E F n r i j f A Z →
        ∃ B C, M.mem B Z ∧ M.mem C Z ∧ Suniform_d I Z U E F n r i j f A C B) := by
    rw [guarded Z U E f hf, index Z U E e f
      ⟨Fin.cases μ (Fin.cases A (fun _ => q)), fun _ => μ⟩ hZ he hE hf
      (Fin.cases hμ (Fin.cases hA (fun _ => hq))), sc_index_sat_l (ZF.modelsKP hZF),
      ← h₃.sat_l I hZF build.program build.root Z U E f, read Z U E e f A hZ he hE hf hA]
    rfl
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  have valid f (hf : M.mem f E) : Ssat_d I X R E F₄ n₄ r₄ f := by
    obtain ⟨A, hA, hsA⟩ := ((hE f).mp hf).2.2 s hs
    obtain ⟨μ, hμ, hσμ⟩ := ((hE f).mp hf).2.2 σ hσω
    obtain ⟨e, he, hτe⟩ := ((hE f).mp hf).2.2 τ hτω
    exact (read' X R E c f A μ e hX hm hE hf hsA hσμ hτe).mpr fun idx =>
      source A hA ⟨μ, e, hμ, he, idx⟩ E F n r i j f A hE hF hr hi hj hij hf hA (fun _ h => h)
  obtain ⟨μ, e, hμ, he, idx⟩ := small
  -- 三次赋值更新均在原支撑之外，原公式及其逐点存在前提保持不变。
  obtain ⟨g₀, u₀, hg₀⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs hD
  obtain ⟨g₁, u₁, hg₁⟩ := senv_update_exists_l I hZF hg₀ hσω hμ
  obtain ⟨g₂, u₂, hg₂⟩ := senv_update_exists_l I hZF hg₁ hτω he
  have ns : ¬ M.mem σ s := fun h => ir σ (uσ σ (tu σ (st σ h)))
  have nt : ¬ M.mem τ s := fun h => ir τ ((hτ τ).mpr (Or.inl (uσ τ (tu τ (st τ h)))))
  have agree : Senv_agree_d I s g g₂ := fun a x ha =>
    (u₀.agree_l I (ir s) a x ha).trans ((u₁.agree_l I ns a x ha).trans (u₂.agree_l I nt a x ha))
  have aslot : M.PairMember I s D g₂ := (u₂.2 s D).mpr (Or.inr ⟨fun eq => ir τ (eq ▸ (hτ s).mpr (Or.inl (uσ s (tu s ht.predecessor_mem)))),
    (u₁.2 s D).mpr (Or.inr ⟨fun eq => ir σ (eq ▸ uσ s (tu s ht.predecessor_mem)),
      (u₀.2 s D).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)
  have mslot : M.PairMember I σ μ g₂ := (u₂.2 σ μ).mpr
    (Or.inr ⟨fun eq => ir τ (eq ▸ hτ.predecessor_mem), (u₁.2 σ μ).mpr (Or.inl ⟨rfl, rfl⟩)⟩)
  have eslot : M.PairMember I τ e g₂ := (u₂.2 τ e).mpr (Or.inl ⟨rfl, rfl⟩)
  have total' := (scollect_agree_l I hZF hF hb hr hi hj hK hg ((hK g₂).mpr hg₂) agree
    (hY D hD) (fun _ h => h)).mp total
  obtain ⟨B, C, hB, hC, hf, select⟩ := (read' Y S K d g₂ D μ e hY hn hK ((hK g₂).mpr hg₂) aslot mslot eslot).mp
    ((hq.valid_l I hZF hω hm.1 hn.1 h₄.program h₄.root hE hK).mp valid g₂ ((hK g₂).mpr hg₂)) idx total'
  exact ⟨B, C, hB, hC, hf, fun x y hxy => (sbin_agree_l I hZF hF hb hr hi hj hK hg ((hK g₂).mpr hg₂)
    agree (hY D hD x (hf.bound_l hxy).1) (hY C hC y (hf.bound_l hxy).2)).mpr (select x y hxy)⟩

/-- 守卫本身是内部公式；传输覆盖新模型中的全部小集合及全部公式参数。 -/
theorem Sc_collection_d.map_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (source : Sc_collection_d I ω X R) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q) : Sc_collection_d I ω Y S := by
  intro D _ small E F n r i j f A hE hF hr hi hj hij hf hA hAD total
  exact sc_collection_forward_l I hZF hω hX hY hm hn hq source hE hF hr hi hj hij hf hA (small.mono_l hAD) total

end YesMetaZFC.SetTheory.Internal
