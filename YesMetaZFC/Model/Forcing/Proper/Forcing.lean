import YesMetaZFC.Model.Forcing.Proper.Name
import YesMetaZFC.Model.Forcing.Proper.Family.Syntax
import YesMetaZFC.Model.Forcing.Proper.Master.Name

/-! # 固定 N[G] 内主加强的存在力迫

使用已经证明的 H(χ) 初等模型 club 捕获定理，将实际提升证书、proper club
名称和 N 内名称转成同一条件上的主加强存在力迫。没有预设后继见证存在。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem force_next_master_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
    {p A T μ u w v ν w' X C} (hp : M.mem p B) (hpz : p ≠ z)
    (hμ : Name_d M B μ) (hu : Name_d M B u) (hw : Name_d M B w) (hv : Name_d M B v) (hν : Name_d M B ν)
    (hLift : Forces_d M B R z hsub_body_m (hsub_env_l w v ν μ) p)
    (hPr : Pr_name_d M B R z p A T w' X C)
    (hwN : Mem_force_d M B R z p w' μ) (hCN : Mem_force_d M B R z p C μ)
    (huN : Mem_force_d M B R z p u μ) (huA : Mem_force_d M B R z p u A) :
    Forces_d M B R z mstr_lower_exists_m (mstr_env_l A T μ u) p := by
  let hZF := ZFC.models_zf_l hZFC
  let ρ₀ := mstr_env_l A T μ u
  let ρ : Env M 10 := (((((ρ₀.push w).push v).push ν).push w').push X).push C
  let eH : Fin 4 → Term 10 := Fin.cases (.bound 7) (Fin.cases (.bound 3) (Fin.cases (.bound 4) (fun _ => .bound 5)))
  let eP : Fin 5 → Term 10 := Fin.cases (.bound 0) (Fin.cases (.bound 1)
    (Fin.cases (.bound 2) (Fin.cases (.bound 9) (fun _ => .bound 8))))
  let eQ : Fin 4 → Term 10 := Fin.cases (.bound 6) (Fin.cases (.bound 7) (Fin.cases (.bound 8) (fun _ => .bound 9)))
  let φ : Formula 1 10 := .conj (hsub_body_m.bind eH) (.conj (pr_name_body_m.bind eP)
    (.conj (.mem (.bound 2) (.bound 7)) (.conj (.mem (.bound 0) (.bound 7))
    (.conj (.mem (.bound 6) (.bound 7)) (.mem (.bound 6) (.bound 9))))))
  let ψ : Formula 1 10 := mstr_lower_exists_m.bind eQ
  have heH : ∀ i, (eH i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  have heP : ∀ i, (eP i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))
  have heQ : ∀ i, (eQ i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  have hφ : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed, heH, heP]
  have hψ : ψ.FreeClosed := (Definitional.Formula.freeClosed_bind_iff_of_closed _ heQ _).mpr mstr_lower_exists_closed_l
  have valid (K : SetTheory.Structure.{u}) (hK : K.Models ZFC) (η : Env K 10) : Formula.satisfies η (.imp φ ψ) := by
    let J := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
    apply (Formula.satisfies_imp_iff _ _ _).mpr
    intro hh
    obtain ⟨hL, hP, hwN, hCN, huN, huA⟩ := (by
      simpa only [φ, Formula.satisfies_conj_iff] using hh)
    have hL := (hsub_sat_l J hK.1 _ (.bound 3) (.bound 2) (.bound 1) .newest).mp
      ((Formula.satisfies_bind η eH hsub_body_m).mp hL)
    obtain ⟨hω', hP⟩ := (Formula.satisfies_conj_iff _ _ _).mp ((Formula.satisfies_bind η eP pr_name_body_m).mp hP)
    have hω' := (Formula.satisfies_isOmega_iff _ _).mp hω'
    have hP := (pr_base_sat_l J hK.1 _ _ _ _ _ _ _).mp hP
    have hwN := (Formula.satisfies_mem_iff η (.bound 2) (.bound 7)).mp hwN
    have hCN := (Formula.satisfies_mem_iff η (.bound 0) (.bound 7)).mp hCN
    have huN := (Formula.satisfies_mem_iff η (.bound 6) (.bound 7)).mp huN
    have huA := (Formula.satisfies_mem_iff η (.bound 6) (.bound 9)).mp huA
    change Hsub_d J (η.bound 5) (η.bound 4) (η.bound 3) (η.bound 7) at hL
    change K.IsOmega (η.bound 2) at hω'
    change Pr_base_d J (η.bound 2) (η.bound 9) (η.bound 8) (η.bound 9) (η.bound 1) (η.bound 0) at hP
    obtain ⟨hω, hχ, hωχ, hH, hn, c, J', d, S, hM, hSub, hElem⟩ := hL
    have heω : η.bound 2 = η.bound 5 := hK.1.eq_of_same_members _ _
      (fun x => ⟨hω'.2 _ hω.1 x, hω.2 _ hω'.1 x⟩)
    have hP' : Pr_base_d J (η.bound 5) (η.bound 9) (η.bound 8) (η.bound 9) (η.bound 1) (η.bound 0) := heω ▸ hP
    have hwN' : K.mem (η.bound 5) (η.bound 7) := heω ▸ hwN
    obtain ⟨s, hs, hm⟩ := pr_base_master_l hK hω hχ hωχ hH hM hSub hElem hwN' hCN hn hP' huN huA
      (fun he => KP.mem_irrefl_d (ZF.modelsKP (ZFC.models_zf_l hK)) _ (he ▸ huA))
    apply (Formula.satisfies_bind η eQ mstr_lower_exists_m).mpr
    apply (Formula.satisfies_exists_iff _ _).mpr
    exact ⟨s, (Formula.satisfies_conj_iff _ _ _).mpr
      ⟨(Formula.satisfies_mem_iff _ _ _).mpr hs.1, (mstr_lower_sat_l hK.1 _).mpr ⟨hs, hm⟩⟩⟩
  have hρ : ∀ a : Term 10, Name_d M B (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact hPr.1
    | bound i => exact Fin.cases hPr.2.2.2.2.1 (Fin.cases hPr.2.2.2.1 (Fin.cases hPr.2.2.1
        (Fin.cases hν (Fin.cases hv (Fin.cases hw (Fin.cases hu (Fin.cases hμ (Fin.cases hPr.2.1 (fun _ => hPr.1))))))))) i
  have hLH : Forces_d M B R z (hsub_body_m.bind eH) ρ p := (forces_bind_l hZF.1 _ _ _ _).mpr
    ((forces_env_l hZF.1 _ hsub_body_closed_l _ _ (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) p).mpr hLift)
  have hLP : Forces_d M B R z (pr_name_body_m.bind eP) ρ p := (forces_bind_l hZF.1 _ _ _ _).mpr
    ((forces_env_l hZF.1 _ pr_name_body_closed_l _ _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))) p).mpr hPr.2.2.2.2.2)
  have hh : Forces_d M B R z φ ρ p := (forces_conj_l _ _ _ _).mpr ⟨hLH, (forces_conj_l _ _ _ _).mpr
    ⟨hLP, (forces_conj_l _ _ _ _).mpr ⟨(forces_mem_l hZF.1 _ _ _ _).mpr hwN,
    (forces_conj_l _ _ _ _).mpr ⟨(forces_mem_l hZF.1 _ _ _ _).mpr hCN,
    (forces_conj_l _ _ _ _).mpr ⟨(forces_mem_l hZF.1 _ _ _ _).mpr huN, (forces_mem_l hZF.1 _ _ _ _).mpr huA⟩⟩⟩⟩⟩
  have himp := forces_valid_l O hZFC (.imp φ ψ) (by simpa only [Definitional.Formula.FreeClosed] using And.intro hφ hψ)
    valid ρ (fun i => hρ (.bound i)) hp hpz
  have hf := forces_mp_l hZF.1 (forces_regular_l O hZF φ ρ hρ).1 (forces_regular_l O hZF ψ ρ hρ) hp hpz himp hh
  exact (forces_env_l hZF.1 _ mstr_lower_exists_closed_l _ _
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) p).mp ((forces_bind_l hZF.1 _ _ _ _).mp hf)

/-- 全阶段提升证书与实际 club 名称，自动产生当前阶段的主加强存在力迫。 -/
theorem hlift_master_exists_l {ω δ F G b χ H N w v i A T w' X C u p μ}
    (O : Cond_order_d M B R B) (hZFC : M.Models ZFC) (hLift : Hlift_d M ω δ F G b χ H N w v)
    (hi : M.mem i δ) (hiN : M.mem i N) (hiB : Entry_d M i B F) (hiR : Entry_d M i R G)
    (hb : M.mem b B) (hm : Mstr_d M B R B N p) (hpb : Entry_d M p b R)
    (hPr : Pr_name_d M B R B p A T w' X C) (hwN : M.mem w' N) (hCN : M.mem C N)
    (hμ : Ng_name_d M B N μ) (hu : Name_d M B u)
    (huN : Mem_force_d M B R B p u μ) (huA : Mem_force_d M B R B p u A) :
    Forces_d M B R B mstr_lower_exists_m (mstr_env_l A T μ u) p := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨ν, hν⟩ := ng_name_exists_l M hZF B H
  have hHsub := hLift.2.2 i B R p ν μ hi hiN hiB hiR O hb hm hpb hν hμ
  have mem {s} (hs : M.mem s N) (hn : Name_d M B s) : Mem_force_d M B R B p s μ :=
    mem_force_entry_l O hZF hm.1 hn hm.1 ((hμ.2 s p).mpr ⟨hs, hn, hm.1⟩) (O.refl p hm.1)
  exact force_next_master_l O hZFC hm.1 hm.2.1 hμ.1 hu
    (check_name_l M (check_range_l M hZF) hb hLift.1)
    (check_name_l M (check_range_l M hZF) hb hLift.2.1) hν.1 hHsub hPr
    (mem hwN hPr.2.2.1) (mem hCN hPr.2.2.2.2.1) huN huA

end YesMetaZFC.Model.Forcing.Internal
