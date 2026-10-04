import YesMetaZFC.SetTheory.LargeCardinal.TreeReflection

/-! # 实际派生测度族与投影协调

对每个种子同时收集唯一的派生超滤，形成模型内函数图。
若 j(p)(b)=a，则 p 的逆像把 a 处的测度精确拉到 b 处；协调性由初等性证明。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ef_family_d (j D S F : M.Domain) : Prop := M.IsSetFunction I F ∧ M.IsDomainOf I S F ∧
  ∀ a U, M.PairMember I a U F ↔ M.mem a S ∧ Ed_filter_d I j a D U

def ef_family_m {d} (j D S F : Term d) : Formula 1 d :=
  .conj (Formula.isFunction 𝒞 F) (.conj (Formula.isDomain 𝒞 S F) (.forallE (.forallE
    (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
      (.conj (.mem (.bound 1) S.weaken.weaken) (ed_filter_m (𝒞 := 𝒞) j.weaken.weaken (.bound 1) D.weaken.weaken .newest))))))
derive_free_closed ef_family_m

theorem ef_family_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j D S F : Term d) :
    Formula.satisfies ρ (ef_family_m (𝒞 := 𝒞) j D S F) ↔
      Ef_family_d I (j.eval ρ) (D.eval ρ) (S.eval ρ) (F.eval ρ) := by
  simp only [ef_family_m, Ef_family_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, ed_filter_sat_l I, Definitional.Term.eval_weaken]
  rfl

theorem ef_family_exists_l (hZF : M.Models ZF) (j D S : M.Domain) : ∃ F, Ef_family_d I j D S F := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  let ρ : Env M 2 := ⟨Fin.cases D (fun _ => j), fun _ => D⟩
  let φ : BinarySchema 2 := { body := ed_filter_m (𝒞 := 𝒞) (.bound 3) (.bound 1) (.bound 2) .newest }
  have sat a U : φ.denote ρ a U ↔ Ed_filter_d I j a D U := ed_filter_sat_l I _ _ _ _ _
  obtain ⟨F, hf, hp⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := S) (target := Q) (fun a _ => (ed_filter_exists_l I hZF j a D).imp fun U hU => (sat a U).mpr hU)
    (fun a _ U V hU hV => ed_filter_unique_l I hZF.1 ((sat a U).mp hU) ((sat a V).mp hV))
    (fun a U _ hU => (hQ U).mpr fun s hs => (hP s).mpr (((sat a U).mp hU s).mp hs).1)
  exact ⟨F, hf.1, hf.2.1, fun a U => (hp a U).trans (and_congr_right fun _ => sat a U)⟩

theorem ef_family_ultra_l (hZF : M.Models ZF) {ω X A Y B j D D' P S F}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hP : M.IsPowerSetOf P D) (hPX : M.mem P X) (hjD : M.PairMember I D D' j)
    (hS : M.MemberSubset S D') (hF : Ef_family_d I j D S F) {a U} (ha : M.PairMember I a U F) :
    FilterZF.Maximal_d (ℳ := M) D U := by
  obtain ⟨haS, hU⟩ := (hF.2.2 a U).mp ha
  obtain ⟨V, hV, hv⟩ := ed_ultrafilter_l I hZF hω h hX hY hP hPX hjD (hS a haS)
  exact ed_filter_unique_l I hZF.1 hV hU ▸ hv

/-- 任何实际投影的逆像都满足派生测度协调方程。 -/
theorem ed_projection_l (hZF : M.Models ZF) {ω δ X C Y E j D D' H H' p p' a b A A' U V}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X C Y E j) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (hY : M.TransitiveSet Y) (hD : M.PairMember I D D' j) (hH : M.PairMember I H H' j)
    (hp : M.PairMember I p p' j) (hf : Fn0_d H D p) (hab : Rd_entry_d b a p')
    (hA : M.MemberSubset A D) (hjA : M.PairMember I A A' j)
    (hU : Ed_filter_d I j a D U) (hV : Ed_filter_d I j b H V) :
    ∃ Z, (∀ x, M.mem x Z ↔ M.mem x H ∧ ∃ y, M.mem y A ∧ Rd_entry_d x y p) ∧
      (M.mem Z V ↔ M.mem A U) := by
  have ht := ZF.v_transitive_l I hZF hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hf' := (spred_function_l I hZF hω h ht hY hH hD hp).mp hf
  let ρ : Env M 2 := ⟨Fin.cases p (fun _ => A), fun _ => A⟩
  let ψ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (rd_entry0_m (.bound 1) .newest (.bound 2)) }
  obtain ⟨Z, hz⟩ := ZF.separation_exists_d hZF ψ ρ H
  have spec x : M.mem x Z ↔ M.mem x H ∧ ∃ y, M.mem y A ∧ Rd_entry_d x y p := by
    rw [hz x]; simp only [ψ, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1]; rfl
  have sub : M.MemberSubset Z H := fun x hx => ((spec x).mp hx).1
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF H
  obtain ⟨Z', _, hjZ⟩ := hj.2.2 Z (ht P (ZF.v_power_mem_l I hZF hX hδ (hj.input_mem_of_pairMember hH) hP) Z ((hP Z).mpr sub))
  let φ : Formula 1 4 := Formula.forallMem (.bound 3) (.iff (.mem .newest (.bound 1))
    (Formula.existsMem (.bound 3) (rd_entry0_m (.bound 1) .newest (.bound 3))))
  have tr := spred_delta_l I hZF hω h ht hY φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.iff (.mem _ _) (.existsMem _ (rd_entry0_delta_l ..))))
    ⟨Fin.cases Z (Fin.cases p (Fin.cases A (fun _ => H))), fun _ => H⟩
    ⟨Fin.cases Z' (Fin.cases p' (Fin.cases A' (fun _ => H'))), fun _ => H'⟩
    (Fin.cases hjZ (Fin.cases hp (Fin.cases hjA (fun _ => hH))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1] at tr
  have target : ∀ x, M.mem x H' → (M.mem x Z' ↔ ∃ y, M.mem y A' ∧ Rd_entry_d x y p') :=
    tr.mp (fun x hx => (spec x).trans ⟨And.right, fun hy => ⟨hx, hy⟩⟩)
  refine ⟨Z, spec, (ed_filter_member_l I hj.1 hV sub hjZ).trans
    (((target b (hf'.bound_l hab).1).trans ?_).trans (ed_filter_member_l I hj.1 hU hA hjA).symm)⟩
  exact ⟨fun ⟨y, hy, hby⟩ => (hf'.2.2 b (hf'.bound_l hab).1 y (hf'.bound_l hby).2
    a (hf'.bound_l hab).2 hby hab) ▸ hy, fun ha => ⟨a, ha, hab⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
