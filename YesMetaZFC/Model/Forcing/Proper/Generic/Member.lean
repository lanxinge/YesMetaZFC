import YesMetaZFC.Model.Forcing.Proper.Generic.AtomicDecision

/-! # 主条件下的 N 内名称成员见证

N 中的两个名称若在泛型中满足隶属，主条件先在 N 中遇到原子判定集；
其否定分支不可能发生。初等性再把带权子名称和权重同时取回 N。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
variable {ω χ H c T : M.Domain} (hω : M.IsOmega ω)
  (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ) (hωχ : M.mem ω χ)
  (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
  (hT : ∀ x y, M.PairMember (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
local notation "htr" => ZF.h_transitive_l I hZF hH
include hω hχ hωχ hH hT

theorem selem_wit_pick_l {d N S B R z p s t} (hS : Ssub_d I c d H T N S) (he : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N) (hp : M.mem p N)
    (hsN : M.mem s N) (htN : M.mem t N) (hs : Name_d M B s) (ht : Name_d M B t)
    (hw : Wit_d M false B R z p s t) : ∃ a b, M.mem a N ∧ M.mem b N ∧ Entry_d M a b t ∧
      Entry_d M p b R ∧ Eq_force_d M B R z p s a := by
  let A := smdl_structure_l I (R := T) hS.source.2.1
  let K := smdl_structure_l I (R := S) hS.target.2.1
  let ρ : Env A 6 := (((((⟨fun _ => ⟨B, hS.subset B hB⟩, fun _ => ⟨B, hS.subset B hB⟩⟩ : Env A 1).push
    ⟨R, hS.subset R hR⟩).push ⟨z, hS.subset z hz⟩).push ⟨s, hS.subset s hsN⟩).push
    ⟨t, hS.subset t htN⟩).push ⟨p, hS.subset p hp⟩
  let η : Env K 6 := (((((⟨fun _ => ⟨B, hB⟩, fun _ => ⟨B, hB⟩⟩ : Env K 1).push ⟨R, hR⟩).push
    ⟨z, hz⟩).push ⟨s, hsN⟩).push ⟨t, htN⟩).push ⟨p, hp⟩
  let θ : BinarySchema 6 := {
    body := .conj (entry_m (.bound 1) .newest (.bound 3))
      (.conj (entry_m (.bound 2) .newest (.bound 6))
        (eq_force_m (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 4) (.bound 1))) }
  have hθ (a b : A.Domain) : θ.denote ρ a b ↔ Entry_d M a.val b.val t ∧
      Entry_d M p b.val R ∧ Eq_force_d M B R z p s a.val := by
    simp only [BinarySchema.denote, θ, Formula.satisfies_conj_iff,
      entry_sat_l A (smem_ext_l I hS.source hT htr hZF.1), eq_force_sat_l A (smem_ext_l I hS.source hT htr hZF.1)]
    change (Entry_d A a b (ρ.bound 1) ∧ Entry_d A (ρ.bound 0) b (ρ.bound 4) ∧
      Eq_force_d A (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 0) (ρ.bound 2) a) ↔ _
    rw [smem_entry_l I hS.source hT htr a b (ρ.bound 1), smem_entry_l I hS.source hT htr (ρ.bound 0) b (ρ.bound 4)]
    exact and_congr_right fun hab => and_congr Iff.rfl
      (smem_eq_force_l hZFC hω hχ hωχ hH hS.source hT _ _ _ _ _ a hs (name_entry_l M ht hab).1)
  obtain ⟨a, b, hab, hpb, hea⟩ := hw
  let a' : A.Domain := ⟨a, (trans_entry_l htr (hS.subset t htN) hab).1⟩
  let b' : A.Domain := ⟨b, (trans_entry_l htr (hS.subset t htN) hab).2⟩
  have hρη : ∀ i, (ρ.bound i).val = (η.bound i).val :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  obtain ⟨aN, bN, habN⟩ := selem_binary_witness_l I hZF hω hS he θ ρ η hρη
    ⟨a', b', (hθ a' b').mpr ⟨hab, hpb, hea⟩⟩
  exact ⟨aN.val, bN.val, aN.property, bN.property, (hθ _ _).mp habN⟩

/-- 泛型中的隶属可由 N 内的实际带权条目见证，且权重仍被泛型接受。 -/
theorem ng_member_pick_l {d N S B R z q s t} (O : Cond_order_d M B R z) {U}
    (hU : Generic_d M B R z U) (hS : Ssub_d I c d H T N S) (he : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N) (hsN : M.mem s N) (htN : M.mem t N)
    (hm : Mstr_d M B R z N q) (hq : U q)
    {x y : (extension_l M hZF B R z U).Domain} (hs : Qval_d M B R z U s x) (ht : Qval_d M B R z U t y)
    (hxy : x ∈ y) : ∃ a b, M.mem a N ∧ M.mem b N ∧ Entry_d M a b t ∧ U b ∧ Qval_d M B R z U a x := by
  obtain ⟨D, hDN, hD⟩ := selem_at_dec_l hZFC hω hχ hωχ hH hT hS he hB hR hz hsN htN (qval_name_l hs) (qval_name_l ht)
  obtain ⟨p, hpN, hpD, hpU⟩ := mstr_generic_l hZF hU hq hm hDN (at_dec_dense_l O hD)
  have hp := hU.proper p hpU
  have hw : Wit_d M false B R z p s t := by
    rcases ((hD.2 p hp.1).mp hpD).2 with hw | hn
    · exact hw
    · obtain ⟨v, hvU, hv⟩ := (qval_mem_forcing_l O hZF hU hs ht).mpr hxy
      obtain ⟨r, hrU, hrp, hrv⟩ := hU.directed p v hpU hvU
      have hr := hU.proper r hrU
      obtain ⟨w, a, b, hwr, hab, hwb, he⟩ := hv.2 r ⟨hr.1, hr.2, hrv⟩
      exact (hn w (below_trans_l O hp.1 hwr ⟨hr.1, hr.2, hrp⟩) ⟨a, b, hab, hwb, he⟩).elim
  obtain ⟨a, b, haN, hbN, hab, hpb, heq⟩ := selem_wit_pick_l hZFC hω hχ hωχ hH hT
    hS he hB hR hz hpN hsN htN (qval_name_l hs) (qval_name_l ht) hw
  have ha := (name_entry_l M (qval_name_l ht) hab).1
  obtain ⟨v, hav⟩ := name_value_l (R := R) (z := z) (U := U) ha
  have hvx := (qval_eq_l O hZF hU hs hav).mp ⟨p, hpU, heq⟩
  exact ⟨a, b, haN, hbN, hab, hU.upward p b hpU (name_entry_l M (qval_name_l ht) hab).2 hpb, hvx.symm ▸ hav⟩

end YesMetaZFC.Model.Forcing.Internal
