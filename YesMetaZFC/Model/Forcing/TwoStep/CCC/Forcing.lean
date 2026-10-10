import YesMetaZFC.Model.Forcing.TwoStep.CCC.IndexCountable
import YesMetaZFC.Model.Forcing.CCC.Syntax
import YesMetaZFC.Model.Forcing.CCC.Name

/-! # 反链索引名称被迫可数

把第二阶段 CCC 与实际索引图同时反射，再由每个泛型中的真实单射推出原力迫
证书。原模型不需要已经存在泛型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S D t g ω w : M.Domain}

theorem step_index_forces_countable_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (h : Two_step_d M B R z b A T W C S) (hT : Name_d M B T)
    (hP : Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) b)
    (hC : Forces_d M B R z (ccc_exists_m (.bound 0) (.bound 1)) (ord_env_l M A T) b)
    (hd : Antichain_d M C S C D) (ht : Name_d M B t) (hg : Name_d M B g)
    (hi : Step_index_d M B b D t g) (hω : M.IsOmega ω) (hw : Check_d M b ω w)
    (hwn : Name_d M B w) (hb : b ≠ z) :
    Forces_d M B R z (Formula.cardinalLessOrEqual kpair_convention_l (.bound 0) (.bound 1))
      (ord_env_l M t w) b := by
  let ρ : Env M 14 := (((((((((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push A).push T).push W).push C).push S).push D).push t).push g).push ω).push w
  let pre : Formula 1 2 := preord_m (.bound 0) (.bound 1)
  let ccc : Formula 1 2 := ccc_exists_m (.bound 0) (.bound 1)
  let names : Fin 2 → Term 14 := Fin.cases (.bound 9) (fun _ => .bound 8)
  let α : Formula 1 14 := .conj (two_step_m (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5))
    (.conj (name_m (.bound 13) (.bound 8)) (.conj (force_at_m pre names (.bound 13) (.bound 12) (.bound 11) (.bound 10))
      (.conj (force_at_m ccc names (.bound 13) (.bound 12) (.bound 11) (.bound 10))
        (.conj (antichain_m (.bound 6) (.bound 5) (.bound 6) (.bound 4))
          (.conj (step_index_m (.bound 13) (.bound 10) (.bound 4) (.bound 3) (.bound 2))
            (.conj (name_m (.bound 13) (.bound 2)) (.conj (Formula.isOmega (.bound 1)) (check_m (.bound 10) (.bound 1) (.bound 0)))))))))
  have raw (N : SetTheory.Structure.{u}) (hE : Extensional N) (η : Env N 14) :
      Formula.satisfies η α ↔
      Two_step_d N (η.bound 13) (η.bound 12) (η.bound 11) (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 7) (η.bound 6) (η.bound 5) ∧
      Name_d N (η.bound 13) (η.bound 8) ∧
      Forces_d N (η.bound 13) (η.bound 12) (η.bound 11) pre ⟨fun i => (names i).eval η, η.free⟩ (η.bound 10) ∧
      Forces_d N (η.bound 13) (η.bound 12) (η.bound 11) ccc ⟨fun i => (names i).eval η, η.free⟩ (η.bound 10) ∧
      Antichain_d N (η.bound 6) (η.bound 5) (η.bound 6) (η.bound 4) ∧
      Step_index_d N (η.bound 13) (η.bound 10) (η.bound 4) (η.bound 3) (η.bound 2) ∧
      Name_d N (η.bound 13) (η.bound 2) ∧ N.IsOmega (η.bound 1) ∧ Check_d N (η.bound 10) (η.bound 1) (η.bound 0) := by
    simp only [α, Formula.satisfies_conj_iff, two_step_sat_l hE, name_sat_l N hE,
      force_at_sat_l, antichain_sat_l N hE, step_index_sat_l hE, Formula.satisfies_isOmega_iff, check_sat_l N hE]
    rfl
  have hpre : pre.FreeClosed := preord_m_freeClosed _ _ rfl rfl
  have hccc : ccc.FreeClosed := ccc_exists_m_freeClosed _ _ rfl rfl
  have hn : ∀ i, (names i).freeSupport = [] := Fin.cases rfl (fun _ => rfl)
  have hα : α.FreeClosed := by
    simp only [α, Definitional.Formula.FreeClosed]
    exact ⟨two_step_m_freeClosed _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      name_m_freeClosed _ _ rfl rfl, force_at_closed_l _ _ _ _ _ _ hpre hn rfl rfl rfl rfl,
      force_at_closed_l _ _ _ _ _ _ hccc hn rfl rfl rfl rfl,
      antichain_m_freeClosed _ _ _ _ rfl rfl rfl rfl, step_index_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl,
      name_m_freeClosed _ _ rfl rfl, Formula.isOmega_freeClosed _ rfl, check_m_freeClosed _ _ _ rfl rfl rfl⟩
  let φ : Formula 1 2 := Formula.cardinalLessOrEqual kpair_convention_l (.bound 0) (.bound 1)
  have hφ : φ.FreeClosed := Formula.cardinalLessOrEqual_freeClosed _ _ _ rfl rfl
  let es : Fin 2 → Term 14 := Fin.cases (.bound 3) (fun _ => .bound 0)
  have henv (N : SetTheory.Structure.{u}) (hE : Extensional N) (η : Env N 14) (ψ : Formula 1 2) (hψ : ψ.FreeClosed) p :
      Forces_d N (η.bound 13) (η.bound 12) (η.bound 11) ψ ⟨fun i => (names i).eval η, η.free⟩ p ↔
      Forces_d N (η.bound 13) (η.bound 12) (η.bound 11) ψ (ord_env_l N (η.bound 9) (η.bound 8)) p :=
    forces_env_l hE ψ hψ _ _ (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) p
  have result := forces_of_generics_l φ hφ α hα es (.bound 13) (.bound 12) (.bound 11) (.bound 10)
    (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl
    (fun N hN η L _ _ _ hraw U hU hbU ξ hv => ?_) hZF ρ O
    (Fin.cases ht (fun _ => hwn)) h.base hb
    ((raw M hZF.1 ρ).mpr ⟨h, hT, (henv M hZF.1 ρ pre hpre b).mpr hP,
      (henv M hZF.1 ρ ccc hccc b).mpr hC, hd, hi, hg, hω, hw⟩)
  · exact (forces_env_l hZF.1 φ hφ _ (ord_env_l M t w)
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) b).mp result
  · obtain ⟨hs, hTn, hpre', hccc', ha, hidx, hgn, hωN, hcheck⟩ := (raw N hN.1 η).mp hraw
    have hpre' := (henv N hN.1 η pre hpre _).mp hpre'
    have hccc' := (henv N hN.1 η ccc hccc _).mp hccc'
    let E := extension_l N hN (η.bound 13) (η.bound 12) (η.bound 11) U
    have hE := preserves_zf_l L hN hU
    let J := kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hE))
    obtain ⟨Q, hQ⟩ := name_value_l (R := η.bound 12) (z := η.bound 11) (U := U) (show Name_d N (η.bound 13) (η.bound 9) from ⟨_, hs.root, hs.closed⟩)
    obtain ⟨V, hV⟩ := name_value_l (R := η.bound 12) (z := η.bound 11) (U := U) hTn
    obtain ⟨G, hG⟩ := name_value_l (R := η.bound 12) (z := η.bound 11) (U := U) hgn
    have hval : Env_val_d hN (ord_env_l N (η.bound 9) (η.bound 8)) (ord_env_l E Q V) := by
      intro v
      cases v with
      | free _ => exact hV
      | bound i => exact Fin.cases hQ (fun _ => hV) i
    obtain ⟨ν, hν, hcE⟩ := (ccc_exists_sat_l J hE.1 _ _ _).mp
      ((forcing_truth_l L hN hU ccc hccc _ _ hval).mp ⟨_, hbU, hccc'⟩)
    obtain ⟨e, he, hm, hinj⟩ := check_map_l L hN hU hbU
    have hωE := image_omega_l (hEN := hE.1) e hinj hm hN (internal_foundation_l L hN hU) hωN
      (fun X => KP.difference_exists_d (ZF.modelsKP hE) X (e (η.bound 1)))
    have heq := hE.1.eq_of_same_members ν (e (η.bound 1))
      (fun x => ⟨hν.2 _ hωE.1 x, hωE.2 _ hν.1 x⟩)
    have hwv := qval_unique_l (he _ _ hcheck) (hv 1)
    apply (Formula.satisfies_cardinalLessOrEqual_iff J hE.1 ξ _ _).mpr
    change E.CardinalLessOrEqual J (ξ.bound 0) (ξ.bound 1)
    rw [← heq.trans hwv]
    exact step_index_countable_l L hN hU hs (two_step_order_l L hN hs hTn hpre')
      ha hidx e hinj he hQ hV (hv 0) hG (two_step_preord_l L hN hU hQ hV hbU hpre').1 hcE

end YesMetaZFC.Model.Forcing.Internal
