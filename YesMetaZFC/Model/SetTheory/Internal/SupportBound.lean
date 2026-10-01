import YesMetaZFC.Model.SetTheory.Internal.SupportSyntax

/-! # 每个内部有限程序都有内部有限坐标界

固定程序，对其前缀长度作实际原公式的 ω 归纳。后继步只加入当前行的两个
坐标，故已有界与新坐标可由另一个内部自然数同时界住。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem scoord_unique_l {F r i j k l} (hF : M.IsSetFunction I F)
    (h : Scoord_d I F r i j) (g : Scoord_d I F r k l) : i = k ∧ j = l := by
  obtain ⟨c, o, a, hc, ho, ha⟩ := h
  obtain ⟨d, p, b, hd, hp, hb⟩ := g
  have he := hF.2 r c d hc hd
  subst d
  obtain ⟨_, rfl⟩ := I.injective ho hp
  exact I.injective ha hb

theorem sbound_exists_l (hZF : M.Models ZF) {ω n F} (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) :
    ∃ b, M.mem b ω ∧ Sbound_d I F b := by
  classical
  have upper {a b} (ha : M.mem a ω) (hb : M.mem b ω) : ∃ d, M.mem d ω ∧ M.mem a d ∧ M.mem b d := by
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare a ha b hb with he | hab | hba
    · have he := hZF.1.eq_of_same_members a b he
      subst a
      obtain ⟨d, hd, hdω⟩ := hω.1.2 b hb
      exact ⟨d, hdω, hd.predecessor_mem, hd.predecessor_mem⟩
    · obtain ⟨d, hd, hdω⟩ := hω.1.2 b hb
      exact ⟨d, hdω, (hd a).mpr (Or.inl hab), hd.predecessor_mem⟩
    · obtain ⟨d, hd, hdω⟩ := hω.1.2 a ha
      exact ⟨d, hdω, hd.predecessor_mem, (hd b).mpr (Or.inl hba)⟩
  have enlarge {b i j} (hb : M.mem b ω) (hi : M.mem i ω) (hj : M.mem j ω) :
      ∃ d, M.mem d ω ∧ M.MemberSubset b d ∧ M.mem i d ∧ M.mem j d := by
    obtain ⟨e, he, hbe, hie⟩ := upper hb hi
    obtain ⟨d, hd, hed, hjd⟩ := upper he hj
    have heD := (hω.members_areOrdinals hZF d hd).transitive e hed
    exact ⟨d, hd, fun x hx => heD x ((hω.members_areOrdinals hZF e he).transitive b hbe x hx), heD i hie, hjd⟩
  have row {r c} (hr : M.mem r ω) (hc : M.PairMember I r c F) :
      ∃ i j, Scoord_d I F r i j ∧ M.mem i ω ∧ M.mem j ω := by
    have op {k i j} (hs : Sop_d I k c i j) (hi : M.mem i ω) (hj : M.mem j ω) :
        ∃ i j, Scoord_d I F r i j ∧ M.mem i ω ∧ M.mem j ω := by
      obtain ⟨a, o, _, ha, ho⟩ := hs
      exact ⟨i, j, ⟨c, o, a, hc, ho, ha⟩, hi, hj⟩
    rcases hF.2.2 r c hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
    · exact op hs hi hj
    · exact op hs hi hj
    · exact op hs (hω.transitive hZF r hr i hi) (hω.transitive hZF r hr j hj)
    · exact op hs hi (hω.transitive hZF r hr j hj)
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push F
  let φ : UnarySchema 2 := {
    body := .existsE (.conj (.mem .newest (.bound 3)) (.forallE (.forallE (.forallE
      (.imp (.mem (.bound 2) (.bound 4)) (.imp (scoord_m (𝒞 := 𝒞) (.bound 5) (.bound 2) (.bound 1) .newest)
        (.conj (.mem (.bound 1) (.bound 3)) (.mem .newest (.bound 3))))))))) }
  have hφ m : φ.denote ρ m ↔ ∃ b, M.mem b ω ∧
      ∀ r i j, M.mem r m → Scoord_d I F r i j → M.mem i b ∧ M.mem j b := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, scoord_sat_l I]
    rfl
  have bound : ∀ m, M.mem m ω → ∃ b, M.mem b ω ∧
      ∀ r i j, M.mem r m → Scoord_d I F r i j → M.mem i b ∧ M.mem j b := by
    apply hω.induction (fun m => ∃ b, M.mem b ω ∧
      ∀ r i j, M.mem r m → Scoord_d I F r i j → M.mem i b ∧ M.mem j b)
    · obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨D, fun m => (hD m).trans (and_congr_right fun _ => hφ m)⟩
    · intro e he
      obtain ⟨b, _, hb⟩ := hω.1.1
      exact ⟨b, hb, fun r _ _ hr _ => (he r hr).elim⟩
    · rintro m hm ⟨b, hb, hbound⟩ s hs
      by_cases hx : ∃ c, M.PairMember I m c F
      · obtain ⟨c, hc⟩ := hx
        obtain ⟨i, j, hij, hi, hj⟩ := row hm hc
        obtain ⟨d, hd, hbd, hid, hjd⟩ := enlarge hb hi hj
        refine ⟨d, hd, fun r a b hr hab => ?_⟩
        rcases (hs r).mp hr with hr | hr
        · exact ⟨hbd a (hbound r a b hr hab).1, hbd b (hbound r a b hr hab).2⟩
        · have he := hZF.1.eq_of_same_members r m hr
          subst r
          obtain ⟨rfl, rfl⟩ := scoord_unique_l I hF.2.1.2.1 hab hij
          exact ⟨hid, hjd⟩
      · refine ⟨b, hb, fun r i j hr hc => ?_⟩
        rcases (hs r).mp hr with hr | hr
        · exact hbound r i j hr hc
        · have he := hZF.1.eq_of_same_members r m hr
          subst r
          obtain ⟨c, _, _, hc, _⟩ := hc
          exact (hx ⟨c, hc⟩).elim
  obtain ⟨b, hb, hh⟩ := bound n hF.1
  refine ⟨b, hb, fun r i j hr => hh r i j ?_ hr⟩
  obtain ⟨c, _, _, hc, _⟩ := hr
  exact (hF.2.1.2.2 r).mpr ⟨c, hc⟩

end YesMetaZFC.SetTheory.Internal
