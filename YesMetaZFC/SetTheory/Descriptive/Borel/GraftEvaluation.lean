import YesMetaZFC.SetTheory.Descriptive.Borel.GraftWellFounded

/-! # 子树拼接保持求值

比较新旧两棵树的实际求值集。比较性质是原公式，对旧树使用内部良基归纳，
因而即使外部看来有非标准长路径，也不影响本层结论。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bgraft_eval_l (hZF : M.Models ZF) {ω A S z H E T R N F i U V Q G x D W}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F)
    (hc : Bsub_d I H i U V Q G) (hD : Bsem_d I T R N F x D) (hW : Bsem_d I U V Q G x W) :
    ∀ s, M.mem s U → ∀ t, Cons_d I z i s t → (M.mem t D ↔ M.mem s W) := by
  obtain ⟨hi, hU⟩ := bsub_valid_l I hH hc
  let ρ : Env M 4 := (((⟨fun _ => z, fun _ => z⟩ : Env M 1).push i).push D).push W
  let φ : UnarySchema 4 := {
    body := .forallE (.imp (cons_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 1) .newest)
      (.iff (.mem .newest (.bound 3)) (.mem (.bound 1) (.bound 2)))) }
  have hp s : φ.denote ρ s ↔ ∀ t, Cons_d I z i s t → (M.mem t D ↔ M.mem s W) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      cons_sat_l I hZF.1, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff]; rfl
  have hall := wf_rel_ind_l hZF hU.wf φ ρ (fun s hs ih => (hp s).mpr (by
    intro t ht
    have shift : Bshift_d I z H t s Q G := ⟨i, U, V, hc, hs, ht⟩
    have htT := (hG.nodes t).mpr (Or.inr ⟨s, Q, G, shift⟩)
    have neg := bgraft_negs_l I hZF hω hA hz hH hG shift
    have lab := bgraft_labels_l I hZF hω hA hz hH hG shift
    have lit : Blit_d I F x t ↔ Blit_d I G x s := exists_congr fun v => and_congr_left fun _ => lab v
    have uni : Buni_d I N F t ↔ Buni_d I Q G s :=
      and_congr (not_congr neg) (not_congr (exists_congr lab))
    have child : (∃ b, M.mem b T ∧ Rd_entry_d b t R ∧ M.mem b D) ↔
        ∃ r, M.mem r U ∧ Rd_entry_d r s V ∧ M.mem r W := by
      constructor
      · rintro ⟨b, _, hb, hbD⟩
        obtain ⟨r, hr, hrb, hrs⟩ := (bgraft_child_l I hZF hω hA hz hH hG hc hs ht b).mp hb
        exact ⟨r, hr, hrs, ((hp r).mp (ih r hr hrs) b hrb).mp hbD⟩
      · rintro ⟨r, hr, hrs, hrW⟩
        obtain ⟨n, hn, hrf⟩ := (hA r).mp (hU.tree.1 r hr)
        obtain ⟨_, b, _, _, _, hb⟩ := cons_exists_l I hZF hω hz hi hn hrf
        have hbR := (bgraft_child_l I hZF hω hA hz hH hG hc hs ht b).mpr ⟨r, hr, hb, hrs⟩
        exact ⟨b, ((hG.edges.2 t b).mp hbR).2.1, hbR, ((hp r).mp (ih r hr hrs) b hb).mpr hrW⟩
    exact (bsem_node_l I hD htT).trans ((or_congr lit
      (or_congr (and_congr neg (not_congr child)) (and_congr uni child))).trans (bsem_node_l I hW hs).symm)))
  exact fun s hs => (hp s).mp (hall s hs)

theorem bgraft_value_l (hZF : M.Models ZF) {ω A S z H E T R N F x D}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F) (hD : Bsem_d I T R N F x D) :
    M.mem z D ↔
      (M.mem z E ∧ ¬ ∃ i c, M.PairMember I i c H ∧ Bsat_d I ω A S c x) ∨
      (¬ M.mem z E ∧ ∃ i c, M.PairMember I i c H ∧ Bsat_d I ω A S c x) := by
  have child : (∃ b, M.mem b T ∧ Rd_entry_d b z R ∧ M.mem b D) ↔
      ∃ i c, M.PairMember I i c H ∧ Bsat_d I ω A S c x := by
    constructor
    · rintro ⟨b, _, hbR, hbD⟩
      obtain ⟨i, U, V, Q, G, hc, hb⟩ := (bgraft_root_child_l I hZF hω hA hz hzω hH hG b).mp hbR
      obtain ⟨_, hU⟩ := bsub_valid_l I hH hc
      obtain ⟨W, hW, _⟩ := bsem_exists_unique_l I hZF hU.wf Q G x
      have hzW := (bgraft_eval_l I hZF hω hA hz hH hG hc hD hW z (bsub_root_l I hZF.1 hz hH hc) b hb).mp hbD
      obtain ⟨c, hic, hp⟩ := hc
      exact ⟨i, c, hic, (bsat_root_l I hZF hp hU hW hz).mpr hzW⟩
    · rintro ⟨i, c, hic, hx⟩
      obtain ⟨hi, U, V, Q, G, hp, hU⟩ := hH.2 i c hic
      have hc : Bsub_d I H i U V Q G := ⟨c, hic, hp⟩
      obtain ⟨W, hW, _⟩ := bsem_exists_unique_l I hZF hU.wf Q G x
      obtain ⟨_, b, _, _, _, hb⟩ := cons_exists_l I hZF hω hz hi hzω (ds_empty_fun_l I hz)
      have hbR := (bgraft_root_child_l I hZF hω hA hz hzω hH hG b).mpr ⟨i, U, V, Q, G, hc, hb⟩
      have hzW := (bsat_root_l I hZF hp hU hW hz).mp hx
      exact ⟨b, ((hG.edges.2 z b).mp hbR).2.1, hbR,
        (bgraft_eval_l I hZF hω hA hz hH hG hc hD hW z (bsub_root_l I hZF.1 hz hH hc) b hb).mpr hzW⟩
  obtain ⟨neg, lab⟩ := bgraft_root_l I hZF hω hA hz hH hG
  have lit : ¬ Blit_d I F x z := fun ⟨s, hs, _⟩ => lab ⟨s, hs⟩
  have uni : Buni_d I N F z ↔ ¬ M.mem z E := ⟨fun h => fun he => h.1 (neg.mpr he),
    fun h => ⟨fun hn => h (neg.mp hn), lab⟩⟩
  have h := (bsem_node_l I hD ((hG.nodes z).mpr (Or.inl rfl))).trans
    (or_congr Iff.rfl (or_congr (and_congr neg (not_congr child)) (and_congr uni child)))
  simpa only [lit, false_or] using h

end YesMetaZFC.SetTheory.Descriptive
