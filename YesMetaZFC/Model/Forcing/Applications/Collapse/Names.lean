import YesMetaZFC.Model.Forcing.Applications.Collapse.Presentation
import YesMetaZFC.Model.Forcing.Internal.Maximum.Basic
import YesMetaZFC.Model.Forcing.Internal.Reflection.Countermodel
import YesMetaZFC.Model.Forcing.Internal.Check.Omega

/-! # 可数部分函数后继的实际名称

任意大小界、源集和目标集名称决定条件集、关系和顶名称。三次最大值选择均返回
规范名称；原 ZFC 的实际塌缩构造同时证明其规格、预序、顶及条件式可数闭性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

def coll_closed_body_m : Formula 1 3 :=
  .imp (Formula.isOmega (.bound 2)) (closed_m (.bound 1) .newest (.bound 1) (.bound 2))

def coll_names_body_m : Formula 1 6 :=
  .conj (coll_spec_m (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 2))
    (.conj ((preord_m .newest (.bound 1) : Formula 1 2).bind (Fin.cases (.bound 1) (fun _ => .bound 2)))
      (.conj ((top_m (.bound 1) (.bound 2) .newest : Formula 1 3).bind (fun i => .bound i.castSucc.castSucc.castSucc))
        (coll_closed_body_m.bind (Fin.cases (.bound 2) (Fin.cases (.bound 1) (fun _ => .bound 5))))))

@[simp] theorem coll_closed_body_closed_l : coll_closed_body_m.FreeClosed := by
  simp -implicitDefEqProofs [coll_closed_body_m, Definitional.Formula.FreeClosed]

@[simp] theorem coll_names_body_closed_l : coll_names_body_m.FreeClosed := by
  simp only [coll_names_body_m, Definitional.Formula.FreeClosed]
  refine ⟨coll_spec_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl, ?_, ?_, ?_⟩
  · exact (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases rfl (fun _ => rfl)) _).mpr
      (preord_m_freeClosed _ _ rfl rfl)
  · exact (Definitional.Formula.freeClosed_bind_iff_of_closed _ (fun _ => rfl) _).mpr
      (top_m_freeClosed _ _ _ rfl rfl rfl)
  · exact (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) _).mpr
      coll_closed_body_closed_l

def coll_names_env_l (w X Y A T t : M.Domain) : Env M 6 :=
  (((((⟨fun _ => w, fun _ => w⟩ : Env M 1).push X).push Y).push T).push A).push t

def Coll_names_d (I : kpair_convention_l.Interpretation M) (B R z w X Y A T t : M.Domain) : Prop :=
  (Name_d M B A ∧ Name_d M B T ∧ Name_d M B t) ∧
    (∀ s, s = A ∨ s = T ∨ s = t → Norm_name_d M I B R z s s) ∧
    ∀ p, M.mem p B → p ≠ z → Forces_d M B R z coll_names_body_m (coll_names_env_l w X Y A T t) p

theorem collapse_names_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {w X Y}
    (hw : Name_d M B w) (hX : Name_d M B X) (hY : Name_d M B Y) : ∃ A T t,
      Coll_names_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC))))
        B R z w X Y A T t := by
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push X).push Y
  let φ : UnarySchema 3 := ⟨.existsE (.existsE coll_names_body_m),
    by simpa only [Definitional.Formula.FreeClosed] using coll_names_body_closed_l⟩
  let ψ : UnarySchema 4 := ⟨.existsE coll_names_body_m,
    by simpa only [Definitional.Formula.FreeClosed] using coll_names_body_closed_l⟩
  let θ : UnarySchema 5 := ⟨coll_names_body_m, coll_names_body_closed_l⟩
  have hρ : ∀ i, Name_d M B (ρ.bound i) := Fin.cases hY (Fin.cases hX (fun _ => hw))
  have valid (N : SetTheory.Structure.{u}) (hN : N.Models ZFC) (η : Env N 3) :
      Formula.satisfies η (.existsE φ.body) := by
    have hZF := ZFC.models_zf_l hN
    let I := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hZF))
    obtain ⟨Q, D, h⟩ := coll_spec_exists_l hZF (η.bound 2) (η.bound 1) (η.bound 0)
    obtain ⟨o, ho⟩ := KP.exists_empty (ZF.modelsKP hZF)
    obtain ⟨hp, htop⟩ := coll_spec_top_l I h ho
    simp only [φ, Formula.satisfies_exists_iff]
    refine ⟨D, Q, o, ?_⟩
    simp only [coll_names_body_m, Formula.satisfies_conj_iff, Formula.satisfies_bind]
    refine ⟨(coll_spec_sat_l I hN.1 _ _ _ _ _ _).mpr h, (preord_sat_l hN.1 _ _ _).mpr hp,
      (top_sat_l hN.1 _ _ _ _).mpr htop, ?_⟩
    simp only [coll_closed_body_m, Formula.satisfies_imp_iff, Formula.satisfies_isOmega_iff,
      closed_sat_l I hN.1]
    exact fun hω => coll_spec_closed_l hN hω h
  obtain ⟨T, hT, hTN, ht⟩ := maximum_l O hZFC φ ρ hρ
  have hTφ p (hp : M.mem p B) (hz : p ≠ z) := (ht p hp hz).mp
    (forces_valid_l O hZFC (.existsE φ.body)
      (by simpa only [φ, Definitional.Formula.FreeClosed] using coll_names_body_closed_l) valid ρ hρ hp hz)
  obtain ⟨A, hA, hAN, ha⟩ := maximum_l O hZFC ψ (ρ.push T) (Fin.cases hT hρ)
  have hAφ p hp hz := (ha p hp hz).mp (hTφ p hp hz)
  obtain ⟨t, ht, htN, hmax⟩ := maximum_l O hZFC θ ((ρ.push T).push A) (Fin.cases hA (Fin.cases hT hρ))
  exact ⟨A, T, t, ⟨hA, hT, ht⟩, fun s hs => hs.elim (fun he => he.symm ▸ hAN)
    (fun hs => hs.elim (fun he => he.symm ▸ hTN) (fun he => he.symm ▸ htN)),
    fun p hp hz => (hmax p hp hz).mp (hAφ p hp hz)⟩

/-- 当大小界是旧 ω 的规范名称时，预序、顶和可数闭性均为实际力迫结论。 -/
theorem collapse_names_closed_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {b ω w X Y A T t p}
    (hω : M.IsOmega ω) (hb : M.mem b B) (hw : Check_d M b ω w) (hp : Below_d M B R z p b)
    (h : Coll_names_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC))))
      B R z w X Y A T t) :
    Forces_d M B R z (preord_m .newest (.bound 1)) (ord_env_l M A T) p ∧
    Forces_d M B R z (top_m (.bound 1) (.bound 2) .newest) (top_env_l A T t) p ∧
    Forces_d M B R z (closed_m (.bound 1) .newest (.bound 1) (.bound 2))
      (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T) p := by
  have hZF := ZFC.models_zf_l hZFC
  have hf := ((forces_conj_l _ _ _ p).mp (h.2.2 p hp.1 hp.2.1)).2
  obtain ⟨hP, ht, hc⟩ := (forces_conj_l _ _ _ p).mp hf |>.imp_right fun h => (forces_conj_l _ _ _ p).mp h
  have hP := (forces_bind_l hZF.1 _ _ _ p).mp hP
  have ht := (forces_bind_l hZF.1 _ _ _ p).mp ht
  have hc := (forces_bind_l hZF.1 _ _ _ p).mp hc
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T
  have hc : Forces_d M B R z coll_closed_body_m ρ p :=
    (forces_env_l hZF.1 _ coll_closed_body_closed_l _ ρ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) p).mp hc
  have hwf := check_omega_force_l O hZF hω hb hw hp
  have hwf : Forces_d M B R z (Formula.isOmega (.bound 2)) ρ p := by
    have hbind : (Formula.isOmega (.newest : Term 1)).bind (fun _ : Fin 1 => (.bound 2 : Term 3)) =
        Formula.isOmega (.bound 2) := by
      simp [Formula.isOmega, Formula.isInductive, Formula.isEmpty, Formula.isSuccessor, Formula.forallMem,
        Formula.extensionalEq, Formula.subset, Definitional.Formula.bind, Definitional.Term.bind,
        Definitional.Term.liftSubstitution, Definitional.Term.newest, Definitional.Term.weaken,
        Definitional.Term.rename, Definitional.TermVector.bind, Formula.pairArguments,
        Fin.cases, Fin.induction, Fin.induction.go]
    have hh := (forces_bind_l hZF.1 (Formula.isOmega .newest) (fun _ : Fin 1 => (.bound 2 : Term 3)) ρ p).mpr
      ((forces_env_l hZF.1 (Formula.isOmega .newest) (Formula.isOmega_freeClosed _ rfl)
        (⟨fun _ => w, fun _ => w⟩ : Env M 1)
        (Definitional.Env.substitute ρ (fun _ : Fin 1 => (.bound 2 : Term 3))) (fun _ => rfl) p).mp hwf)
    exact hbind ▸ hh
  have hn : ∀ a : Term 3, Name_d M B (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact check_name_l M (check_range_l M hZF) hb hw
    | bound i => exact Fin.cases h.1.2.1 (Fin.cases h.1.1 (fun _ => check_name_l M (check_range_l M hZF) hb hw)) i
  exact ⟨(forces_env_l hZF.1 _ (preord_m_freeClosed _ _ rfl rfl) _ _ (Fin.cases rfl (fun _ => rfl)) p).mp hP,
    (forces_env_l hZF.1 _ (top_m_freeClosed _ _ _ rfl rfl rfl) _ _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) p).mp ht,
    forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hn).1 (forces_regular_l O hZF _ ρ hn) hp.1 hp.2.1 hc hwf⟩

end YesMetaZFC.Model.Forcing.Internal
