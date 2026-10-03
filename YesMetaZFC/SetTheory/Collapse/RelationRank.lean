import YesMetaZFC.SetTheory.Collapse.RelationExistence
import YesMetaZFC.SetTheory.RankImage

/-! # 内部良基关系的序数秩

先作实际集合坍塌，再取坍塌值的集合秩。秩像是一个序数，因此可数载体的
全部节点秩有同一个可数序数界；这里不调用可数并的选择原则。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rk_sup_l (hZF : M.Models ZF) {x α} (h : Rk_d I x α) (β : M.Domain) :
    M.mem β α ↔ ∃ y γ, M.mem y x ∧ Rk_d I y γ ∧ (β = γ ∨ M.mem β γ) := by
  classical
  constructor
  · intro hb
    apply Classical.byContradiction
    intro hn
    obtain ⟨V, hv⟩ := ZF.v_exists_l I hZF ((h.ordinal I).mem hb)
    have sub : M.MemberSubset x V := by
      intro y hy
      obtain ⟨γ, hg⟩ := ZF.rk_exists_l I hZF y
      apply (ZF.rk_mem_l I hZF hg hv).mpr
      rcases (h.ordinal I).wellOrder.linear.compare γ (ZF.rk_member_l I hZF hg h hy) β hb with e | e | e
      · exact (hn ⟨y, γ, hy, hg, Or.inl (hZF.1.eq_of_same_members γ β e).symm⟩).elim
      · exact e
      · exact (hn ⟨y, γ, hy, hg, Or.inr e⟩).elim
    obtain ⟨_, _, _, least⟩ := h
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) β (least β V hv sub β hb)
  · rintro ⟨y, γ, hy, hg, rfl | hb⟩
    · exact ZF.rk_member_l I hZF hg h hy
    · exact (h.ordinal I).transitive γ (ZF.rk_member_l I hZF hg h hy) β hb

def Wr_d (X R F : M.Domain) : Prop := M.IsSetFunction I F ∧ M.IsDomainOf I X F ∧
  ∀ a α, M.PairMember I a α F → M.IsOrdinal α ∧ ∀ β, M.mem β α ↔
    ∃ b γ, M.mem b X ∧ Rd_entry_d b a R ∧ M.PairMember I b γ F ∧ (β = γ ∨ M.mem β γ)
def wr_m {d} (X R F : Term d) : Formula 1 d := .conj (Formula.isFunction 𝒞 F) (.conj
  (Formula.isDomain 𝒞 X F) (.forallE (.forallE (.imp
  (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken) (.conj (Formula.isOrdinal .newest)
  (.forallE (.iff (.mem .newest (.bound 1)) (.existsE (.existsE (.conj
  (.mem (.bound 1) X.weaken.weaken.weaken.weaken.weaken) (.conj
  (rd_entry_m (.bound 1) (.bound 4) R.weaken.weaken.weaken.weaken.weaken) (.conj
  (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken.weaken.weaken.weaken)
  (.disj (Formula.extensionalEq (.bound 2) .newest) (.mem (.bound 2) .newest))))))))))))))
derive_free_closed wr_m
theorem wr_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X R F : Term d) :
    Formula.satisfies ρ (wr_m (𝒞 := 𝒞) X R F) ↔ Wr_d I (X.eval ρ) (R.eval ρ) (F.eval ρ) := by
  simp only [wr_m, Wr_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isOrdinal_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, rd_entry_sat_l hE,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]; rfl

theorem wr_exists_l (hZF : M.Models ZF) {X R} (hw : Wf_rel_d X R) :
    ∃ α F, M.IsOrdinal α ∧ M.IsSetFunctionFromTo I F X α ∧ M.IsSetSurjectiveOnto I F X α ∧ Wr_d I X R F := by
  obtain ⟨T, G, hg, step, range, trans⟩ := wc_collapse_l hZF hw
  obtain ⟨α, H, ha, hh, onto, eh⟩ := ZF.rk_image_l I hZF trans
  let ρ : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let φ : BinarySchema 1 := { body := rd_entry_m (.bound 1) .newest (.bound 2) }
  have hp a x : φ.denote ρ a x ↔ Rd_entry_d a x G := rd_entry_sat_l hZF.1 _ _ _ _
  obtain ⟨D, hd, ed⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := X) (target := T)
    (fun a ha => (hg.2.1 a ha).imp fun x hx => (hp a x).mpr hx.2)
    (fun a ha x y hx hy => hg.2.2 a ha x (hg.bound_l ((hp a x).mp hx)).2
      y (hg.bound_l ((hp a y).mp hy)).2 ((hp a x).mp hx) ((hp a y).mp hy))
    (fun _ _ _ hx => (hg.bound_l ((hp _ _).mp hx)).2)
  have eg a x : M.PairMember I a x D ↔ Rd_entry_d a x G := ((ed a x).trans
    (and_congr_right fun _ => hp a x)).trans ⟨And.right, fun h => ⟨(hg.bound_l h).1, h⟩⟩
  obtain ⟨F, hf, ef⟩ := ZF.exists_compositionFunction hZF I hd hh
  have val a β : M.PairMember I a β F ↔ ∃ x, Rd_entry_d a x G ∧ Rk_d I x β := by
    refine (ef a β).trans ⟨?_, ?_⟩
    · rintro ⟨_, x, hx, hβ⟩
      exact ⟨x, (eg a x).mp hx, ((eh x β).mp hβ).2⟩
    · rintro ⟨x, hx, hβ⟩
      exact ⟨(hg.bound_l hx).1, x, (eg a x).mpr hx, (eh x β).mpr ⟨(hg.bound_l hx).2, hβ⟩⟩
  refine ⟨α, F, ha, hf, ?_, hf.1, hf.2.1, fun a β hab => ?_⟩
  · intro β hb
    obtain ⟨x, hx, hxb⟩ := onto β hb
    obtain ⟨a, hax⟩ := (range x).mp hx
    exact ⟨a, (hg.bound_l hax).1, (val a β).mpr ⟨x, hax, ((eh x β).mp hxb).2⟩⟩
  · obtain ⟨x, hax, hr⟩ := (val a β).mp hab
    refine ⟨hr.ordinal I, fun γ => (rk_sup_l I hZF hr γ).trans ⟨?_, ?_⟩⟩
    · rintro ⟨y, δ, hyx, hy, hδ⟩
      obtain ⟨b, hb, hba, hby⟩ := ((step.2 a x hax).2.2 y).mp hyx
      exact ⟨b, δ, hb, hba, (val b δ).mpr ⟨y, hby, hy⟩, hδ⟩
    · rintro ⟨b, δ, hb, hba, hbd, hδ⟩
      obtain ⟨y, hby, hy⟩ := (val b δ).mp hbd
      exact ⟨y, δ, ((step.2 a x hax).2.2 y).mpr ⟨b, hb, hba, hby⟩, hy, hδ⟩

theorem wr_unique_l (hZF : M.Models ZF) {X R F G} (hw : Wf_rel_d X R)
    (hf : Wr_d I X R F) (hg : Wr_d I X R G) : F = G := by
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push G
  let φ : UnarySchema 2 := { body := .forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 4)) (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (Formula.extensionalEq (.bound 1) .newest)))) }
  have hp a : φ.denote ρ a ↔ ∀ α β, M.PairMember I a α F → M.PairMember I a β G → α = β := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have all := wf_rel_ind_l hZF hw φ ρ (fun a _ ih => (hp a).mpr (by
    intro α β ha hb
    apply hZF.1.eq_of_same_members α β
    intro γ
    constructor
    · intro hγ
      obtain ⟨b, δ, hbX, hba, hδ, hγδ⟩ := ((hf.2.2 a α ha).2 γ).mp hγ
      obtain ⟨ε, hε⟩ := (hg.2.1 b).mp hbX
      exact ((hg.2.2 a β hb).2 γ).mpr ⟨b, ε, hbX, hba, hε, (hp b).mp (ih b hbX hba) δ ε hδ hε ▸ hγδ⟩
    · intro hγ
      obtain ⟨b, δ, hbX, hba, hδ, hγδ⟩ := ((hg.2.2 a β hb).2 γ).mp hγ
      obtain ⟨ε, hε⟩ := (hf.2.1 b).mp hbX
      exact ((hf.2.2 a α ha).2 γ).mpr ⟨b, ε, hbX, hba, hε, ((hp b).mp (ih b hbX hba) ε δ hε hδ).symm ▸ hγδ⟩))
  apply hf.1.1.eq_of_pairMember_iff hZF.1 hg.1.1
  intro a α
  constructor
  · intro ha
    have hx := (hf.2.1 a).mpr ⟨α, ha⟩
    obtain ⟨β, hb⟩ := (hg.2.1 a).mp hx
    exact ((hp a).mp (all a hx) α β ha hb).symm ▸ hb
  · intro ha
    have hx := (hg.2.1 a).mpr ⟨α, ha⟩
    obtain ⟨β, hb⟩ := (hf.2.1 a).mp hx
    exact (hp a).mp (all a hx) β α hb ha ▸ hb

theorem wr_countable_l (hZF : M.Models ZF) {ω X R} (hω : M.IsOmega ω)
    (hw : Wf_rel_d X R) (hc : M.CardinalLessOrEqual I X ω) :
    ∃ α F, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ M.IsSetFunctionFromTo I F X α ∧ Wr_d I X R F := by
  obtain ⟨α, F, ha, hf, hs, hr⟩ := wr_exists_l I hZF hw
  exact ⟨α, F, ha, ZF.ordinal_image_bound_l I hZF (hω.isOrdinal hZF) hc hf hs, hf, hr⟩

end YesMetaZFC.SetTheory
