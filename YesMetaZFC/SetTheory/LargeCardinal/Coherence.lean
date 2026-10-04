import YesMetaZFC.SetTheory.LargeCardinal.SupportProjection

/-! # 有限支撑测度函数自身的协调律

每个实际坐标函数 q:m→n 都有实际逆像集合。协调条件只量化函数图与测度成员资格，
其证明从强嵌入构造投影及逆像，不把协调性作为扩展器的额外假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Es_pull_d (m n κ q A Z : M.Domain) : Prop := ∀ s, M.mem s Z ↔
  Fn0_d n κ s ∧ ∃ t, M.mem t A ∧ Cp0_d m n κ q s t

def es_pull_m {d} (m n κ q A Z : Term d) : Formula 1 d := .forallE (.iff (.mem .newest Z.weaken)
  (.conj (fn0_m n.weaken κ.weaken .newest) (Formula.existsMem A.weaken
    (cp0_m m.weaken.weaken n.weaken.weaken κ.weaken.weaken q.weaken.weaken (.bound 1) .newest))))
derive_free_closed es_pull_m

theorem es_pull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (m n κ q A Z : Term d) :
    Formula.satisfies ρ (es_pull_m m n κ q A Z) ↔
      Es_pull_d (m.eval ρ) (n.eval ρ) (κ.eval ρ) (q.eval ρ) (A.eval ρ) (Z.eval ρ) := by
  simp only [es_pull_m, Es_pull_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_existsMem_iff,
    cp0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Es_reindex_d (κ L F m n q a b U V A : M.Domain) : Prop := Fn0_d m n q → Fn0_d n L a →
  Cp0_d m n L q a b → M.PairMember I a V F → M.PairMember I b U F →
  (∀ t, M.mem t A → Fn0_d m κ t) → ∃ Z, Es_pull_d m n κ q A Z ∧ (M.mem Z V ↔ M.mem A U)

def es_reindex_m {d} (κ L F m n q a b U V A : Term d) : Formula 1 d :=
  .imp (fn0_m m n q) (.imp (fn0_m n L a) (.imp (cp0_m m n L q a b)
    (.imp (Formula.orderedPairMem 𝒞 a V F) (.imp (Formula.orderedPairMem 𝒞 b U F)
      (.imp (Formula.forallMem A (fn0_m m.weaken κ.weaken .newest)) (.existsE
        (.conj (es_pull_m m.weaken n.weaken κ.weaken q.weaken A.weaken .newest)
          (.iff (.mem .newest V.weaken) (.mem A.weaken U.weaken)))))))))
derive_free_closed es_reindex_m

theorem es_reindex_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L F m n q a b U V A : Term d) :
    Formula.satisfies ρ (es_reindex_m (𝒞 := 𝒞) κ L F m n q a b U V A) ↔
      Es_reindex_d I (κ.eval ρ) (L.eval ρ) (F.eval ρ) (m.eval ρ) (n.eval ρ) (q.eval ρ)
        (a.eval ρ) (b.eval ρ) (U.eval ρ) (V.eval ρ) (A.eval ρ) := by
  simp only [es_reindex_m, Es_reindex_d, Formula.satisfies_imp_iff, fn0_sat_l hE, cp0_sat_l hE,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, es_pull_sat_l hE, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]
  rfl

def Es_coherent_d (ω κ L F : M.Domain) : Prop := ∀ m n q a b U V A, M.mem m ω → M.mem n ω →
  Es_reindex_d I κ L F m n q a b U V A

def es_coherent_m {d} (ω κ L F : Term d) : Formula 1 d :=
  .forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (.mem (.bound 7) ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
      (.imp (.mem (.bound 6) ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
        (es_reindex_m (𝒞 := 𝒞) κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
          L.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
          (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))))))
derive_free_closed es_coherent_m

theorem es_coherent_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (es_coherent_m (𝒞 := 𝒞) ω κ L F) ↔
      Es_coherent_d I (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [es_coherent_m, Es_coherent_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, es_reindex_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem es_coherent_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F}
    (hω : M.IsOmega ω) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d I ω X C Y E j) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k)
    (hL : M.MemberSubset L k) (hSY : M.MemberSubset S Y) (hF : Es_family_d I j κ L S F) :
    Es_coherent_d I ω κ L F := by
  intro m n q a b U V A hm hn hq ha hb haV hbU hA
  have ht := ZF.v_transitive_l I hZF hX
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  obtain ⟨haS, r, H, hr, hH, hV⟩ := (hF.2.2 a V).mp haV
  obtain ⟨hbS, s, D, hs, hD, hU⟩ := (hF.2.2 b U).mp hbU
  have er := hr.domain_eq_l hZF.1 ha
  have es := hs.domain_eq_l hZF.1 hb.1
  have hH : ∀ t, M.mem t H ↔ Fn0_d n κ t := fun t => er ▸ hH t
  have hD : ∀ t, M.mem t D ↔ Fn0_d m κ t := fun t => es ▸ hD t
  obtain ⟨H', D', p, p', hjH, hjD, hp, spec, hjp, hab⟩ := ed_reindex_l I hZF hω hX hδ h hY hc
    (hc.ordinal.transitive ω hωκ m hm) (hc.ordinal.transitive ω hωκ n hn) hq hH hD hL (hSY a haS) (hSY b hbS) ha hb
  have hAD : M.MemberSubset A D := fun t ht => (hD t).mpr (hA t ht)
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨A', _, hjA⟩ := hj.2.2 A (ht P (ZF.v_power_mem_l I hZF hX hδ (hj.input_mem_of_pairMember hjD) hP)
    A ((hP A).mpr hAD))
  obtain ⟨Z, hz, hUV⟩ := ed_projection_l I hZF hω h hX hδ hY hjD hjH hjp hp hab hAD hjA hU hV
  refine ⟨Z, fun s => (hz s).trans ?_, hUV⟩
  exact ⟨fun ⟨hs, t, ht, hp⟩ => ⟨(hH s).mp hs, t, ht, ((spec s t).mp hp).2⟩,
    fun ⟨hs, t, ht, hc⟩ => ⟨(hH s).mpr hs, t, ht, (spec s t).mpr ⟨(hH s).mpr hs, hc⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
