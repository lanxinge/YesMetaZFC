import YesMetaZFC.SetTheory.InnerModel.Relative.TruthSyntax
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift
import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffModelMinimum
import YesMetaZFC.SetTheory.Descriptive.Game.GameWitness
import YesMetaZFC.Model.SetTheory.Truth.SetTruthReals
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.Model.SetTheory.Images.NaturalBasisImage
import YesMetaZFC.Model.SetTheory.Images.BinaryImage
import YesMetaZFC.Model.Forcing.Ground.Collapse

/-! # L(ℝ) 中 AD 的原句子与实际模型语义

大基数层的 Determinacy/LReal 的 wd_lr_ad_l 以本句子为结论。本层只建立
精确陈述及其语义对应，定义和模型构造不依赖该大基数定理。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

private theorem la_ad_sat_l (S : M.Domain) (hS : M.TransitiveSet S) {d}
    (ρ : Env M d) (T : Term d) (hT : T.eval ρ = S) :
    Formula.satisfies ρ (la_rel_m (ad_m kpair_convention_l) T Fin.elim0) ↔
      (la_model_l S (ZF.models_kpi_l hZF)).SatisfiesSentence Axioms.ad_axiom := by
  let η : Env (la_model_l S (ZF.models_kpi_l hZF)) 0 :=
    ⟨Fin.elim0, fun _ => ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩⟩
  have h := la_rel_sat_l (ZF.models_kpi_l hZF) S hS (ad_m kpair_convention_l) ad_closed_l η ρ T Fin.elim0 hT (fun i => Fin.elim0 i)
  exact h.trans ((ad_sat_l (kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF hS)))
    (la_model_ext_l S (ZF.models_kpi_l hZF) hS) η).trans (ad_axiom_sat_l (ZF.modelsKP (la_model_zf_l S hZF hS))).symm)

def lr_ad_m : Formula 1 0 := .existsE (.existsE (.existsE
  (.conj (baire_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1))
    (.conj (tc_m (.bound 1) .newest)
      (la_rel_m (ad_m kpair_convention_l) .newest Fin.elim0)))))

theorem lr_ad_closed_l : lr_ad_m.FreeClosed := by
  simp only [lr_ad_m, Definitional.Formula.FreeClosed]
  exact ⟨baire_free_l _ _ rfl rfl, tc_m_freeClosed _ _ rfl rfl,
    la_rel_closed_l _ ad_closed_l _ _ rfl (fun i => Fin.elim0 i)⟩

theorem lr_ad_sat_l (ρ : Env M 0) : Formula.satisfies ρ lr_ad_m ↔
    (InnerModel.Relative.lr_model_l hZF).SatisfiesSentence Axioms.ad_axiom := by
  simp only [lr_ad_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    baire_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1, tc_sat_l]
  constructor
  · rintro ⟨ω, B, S, hB, hS, ht⟩
    have h : Lr_seed_d hZF ω B S := ⟨hB, hS⟩
    rw [lr_model_eq_l hZF h]
    exact (la_ad_sat_l hZF S hS.1 _ .newest rfl).mp ht
  · intro ht
    obtain ⟨ω, B, S, h⟩ := lr_seed_exists_l hZF
    rw [lr_model_eq_l hZF h] at ht
    exact ⟨ω, B, S, h.1, h.2, (la_ad_sat_l hZF S h.2.1 _ .newest rfl).mpr ht⟩

/-! 固定任意一个合法种子后，`L(ℝ)` 的 AD 目标精确降为同一载体上的 `L[A]` 目标。 -/
theorem lr_ad_iff_seed_l {ω B S : M.Domain} (h : Lr_seed_d hZF ω B S) :
    (InnerModel.Relative.lr_model_l hZF).SatisfiesSentence Axioms.ad_axiom ↔
      (la_model_l S (ZF.models_kpi_l hZF)).SatisfiesSentence Axioms.ad_axiom := by
  rw [lr_model_eq_l hZF h]

end YesMetaZFC.SetTheory.InnerModel.Relative

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel InnerModel.Relative Descriptive
universe u

def Axioms.lr_ad : Sentence := Sentence.ofFormula lr_ad_m lr_ad_closed_l

theorem lr_ad_axiom_sat_l {M : Structure.{u}} (hZF : M.Models ZF) :
    M.SatisfiesSentence Axioms.lr_ad ↔ (InnerModel.Relative.lr_model_l hZF).SatisfiesSentence Axioms.ad_axiom := by
  rw [Structure.satisfiesSentence_iff]
  constructor
  · intro h
    obtain ⟨x⟩ := M.nonempty
    exact (lr_ad_sat_l hZF ⟨Fin.elim0, fun _ => x⟩).mp (h (fun _ => x))
  · exact fun h f => (lr_ad_sat_l hZF ⟨Fin.elim0, f⟩).mpr h

theorem lr_ad_axiom_of_seed_l {M : Structure.{u}} (hZF : M.Models ZF)
    {ω B S : M.Domain} (seed : Lr_seed_d hZF ω B S)
    (had : (la_model_l S (ZF.models_kpi_l hZF)).SatisfiesSentence Axioms.ad_axiom) :
    M.SatisfiesSentence Axioms.lr_ad := by
  rw [lr_ad_axiom_sat_l hZF, lr_ad_iff_seed_l hZF seed]
  exact had

theorem lr_ad_of_seed_AD_d {M : Structure.{u}} (hZF : M.Models ZF)
    {ω B S : M.Domain} (seed : Lr_seed_d hZF ω B S)
    (had : Descriptive.AD_d
      (InnerModel.kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF seed.2.1)))) :
    M.SatisfiesSentence Axioms.lr_ad := by
  apply lr_ad_axiom_of_seed_l hZF seed
  exact (ad_axiom_sat_l
    (ZF.modelsKP (la_model_zf_l S hZF seed.2.1))).mpr had

theorem lr_ad_of_seed_det_l {M : Structure.{u}} (hZF : M.Models ZF)
    {ω B S : M.Domain} (seed : Lr_seed_d hZF ω B S)
    {ω' B' T' : (la_model_l S (ZF.models_kpi_l hZF)).Domain}
    (hB : Baire_d (kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF seed.2.1))) ω' B')
    (hT : Fseq_space_d (kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF seed.2.1))) ω' ω' T')
    (all : ∀ A, (la_model_l S (ZF.models_kpi_l hZF)).MemberSubset A B' →
      Det_d (kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF seed.2.1))) ω' B' T' A) :
    M.SatisfiesSentence Axioms.lr_ad := by
  apply lr_ad_of_seed_AD_d hZF seed
  exact ⟨ω', B', T', hB, hT, all⟩

end YesMetaZFC.SetTheory

/-! ## 完整旧收益表的有界核验

遍历实际代码方块与 Jensen 图中的条目；合法参数处的表值必须满足
同一个完整收益方程。图对全部旧代码有值，故此有界检查推出全局覆盖，
无需把覆盖性或完整幂集留作见证外的假设。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Jp_table_d (φ : Formula 1 4) (B a c P F t X K H W : M.Domain) : Prop := Fn0_d c P F ∧
  ∀ d, M.mem d c → ∀ p, M.mem p X → ∀ γ, M.mem γ t → ∀ q, M.mem q t →
    ∀ Y, M.mem Y W → ∀ A, M.mem A P → KPair_d M p γ q → Rd_entry_d p d K →
      Rd_entry_d γ Y H → Rd_entry_d d A F → M.mem B Y → M.mem a Y → M.mem q Y → Jp_value_d φ B a q Y A

def jp_table_m {d} (φ : Formula 1 4) (B a c P F t X K H W : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜c⌝ₛ,⌜P⌝ₛ,⌜F⌝ₛ) ∧
  (∀ n ∈ ⌜c⌝ₛ, ∀ p ∈ ⌜X⌝ₛ, ∀ γ ∈ ⌜t⌝ₛ, ∀ q ∈ ⌜t⌝ₛ, ∀ Y ∈ ⌜W⌝ₛ, ∀ A ∈ ⌜P⌝ₛ,
    ⌜kpair0_m⌝ₚ(p,γ,q) → ⌜rd_entry0_m⌝ₚ(p,n,⌜K⌝ₛ) → ⌜rd_entry0_m⌝ₚ(γ,Y,⌜H⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(n,A,⌜F⌝ₛ) → ⌜B⌝ₛ ∈ Y → ⌜a⌝ₛ ∈ Y → q ∈ Y → ⌜(jp_value_m φ)⌝ₚ(⌜B⌝ₛ,⌜a⌝ₛ,q,Y,A))⟫

@[simp] theorem jp_table_closed_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (B a c P F t X K H W : Term d)
    (hb : B.freeSupport = []) (ha : a.freeSupport = []) (hc' : c.freeSupport = [])
    (hp : P.freeSupport = []) (hf : F.freeSupport = []) (ht : t.freeSupport = []) (hx : X.freeSupport = [])
    (hk : K.freeSupport = []) (hh : H.freeSupport = []) (hw : W.freeSupport = []) :
    (jp_table_m φ B a c P F t X K H W).FreeClosed := by
  simp -implicitDefEqProofs [jp_table_m,Definitional.Formula.FreeClosed,hc,hb,ha,hc',hp,hf,ht,hx,hk,hh,hw]

theorem jp_table_delta_l {d} (φ : Formula 1 4) (B a c P F t X K H W : Term d) :
    (jp_table_m φ B a c P F t X K H W).IsDelta0 := by
  refine .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.forallMem _
    (.forallMem _ (.forallMem _ (.forallMem _ ?_))))))
  exact .imp (kpair0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..)
    (.imp (rd_entry0_delta_l ..) (.imp (.mem _ _) (.imp (.mem _ _) (.imp (.mem _ _) (jp_value_delta_l ..)))))))

theorem jp_table_sat_l (hE : Extensional M) {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (ρ : Env M d)
    (B a c P F t X K H W : Term d) : Formula.satisfies ρ (jp_table_m φ B a c P F t X K H W) ↔
      Jp_table_d φ (B.eval ρ) (a.eval ρ) (c.eval ρ) (P.eval ρ) (F.eval ρ) (t.eval ρ)
        (X.eval ρ) (K.eval ρ) (H.eval ρ) (W.eval ρ) := by
  simp only [jp_table_m,Jp_table_d,Formula.satisfies_conj_iff,fn0_sat_l hE,Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff,kpair0_sat_l hE,rd_entry0_sat_l hE,Formula.satisfies_mem_iff,
    jp_value_sat_l φ hc,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem Jp_table_d.cover_l {φ : Formula 1 4} {S B a c P F t X η K D H W : M.Domain}
    (square : Oc_square_d t X η K) (cert : Rc_cert_d ja_op_s (ja_env_l S) D H W)
    (ht : M.mem t D) (hc : M.mem c η) (table : Jp_table_d φ B a c P F t X K H W) :
    ∀ d, M.mem d c → ∀ A, Jp_d I φ S B a d A → Rd_entry_d d A F := by
  intro d hd A present
  have hη := square.2.2.1.transitive c hc d hd
  obtain ⟨p,hp,γ,hγ,q,hq,Y,hY,pair,pc,layer,base,param,index,value⟩ :=
    (jp_local_iff_l hZF square cert ht hη).mp present
  obtain ⟨A',hA',edge⟩ := table.1.2.1 d hd
  have actual := table.2 d hd p hp γ hγ q hq Y hY A' hA' pair pc layer edge base param index
  exact actual.unique_l hZF.1 value ▸ edge

theorem Jp_min_d.table_l {φ : Formula 1 4} (hcφ : φ.FreeClosed) {ω S B T a c t X η K D H W : M.Domain}
    (hw : M.IsOmega ω) (least : Jp_min_d I φ ω S B T a c)
    (square : Oc_square_d t X η K) (cert : Rc_cert_d ja_op_s (ja_env_l S) D H W)
    (ht : M.mem t D) (hc : M.mem c η) :
    ∃ P F, Jp_table_d φ B a c P F t X K H W ∧ ∀ d A, Rd_entry_d d A F → Det_d I ω B T A := by
  obtain ⟨P,F,_,fn,cover,values⟩ := jp_family_l hZF φ hcφ S B a c
  refine ⟨P,F,⟨fn,?_⟩,?_⟩
  · intro d hd p hp γ hγ q hq Y hY A hA pair pc layer edge base param index
    obtain ⟨A',value⟩ := jp_value_exists_l (ZF.modelsKP hZF) φ hcφ B a q Y
    have present : Jp_d I φ S B a d A' :=
      (jp_local_iff_l hZF square cert ht (square.2.2.1.transitive c hc d hd)).mpr
        ⟨p,hp,γ,hγ,q,hq,Y,hY,pair,pc,layer,base,param,index,value⟩
    have same := fn.2.2 d hd A hA A' (fn.bound_l (cover d hd A' present)).2 edge (cover d hd A' present)
    exact same.symm ▸ value
  · intro d A edge
    rcases values d A edge with present | empty
    · exact Classical.byContradiction (fun no => least.2 d (fn.bound_l edge).1 ⟨A,present,no⟩)
    · exact Or.inr (gm_trivial_l I hZF hw empty).2

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 最小坏收益的合并有界检查

实际规范代码方块、原 Jensen 递归证书、当前收益、完整旧收益表及博弈
判断共用一个 Δ₀ 矩阵。全部对象仍由原构造生产，不将覆盖假设留在矩阵外。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}}
def Jp_games_d (ω B T E V c P F A : M.Domain) : Prop := Fn0_d c P F ∧
  ¬ Gs_det_d ω B T E V A ∧ ∀ d, M.mem d c → ∀ D, M.mem D P →
    Rd_entry_d d D F → Gs_det_d ω B T E V D

def jp_games_m {d} (ω B T E V c P F A : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜c⌝ₛ,⌜P⌝ₛ,⌜F⌝ₛ) ∧ ¬ ⌜gs_det_m⌝ₚ(⌜ω⌝ₛ,⌜B⌝ₛ,⌜T⌝ₛ,⌜E⌝ₛ,⌜V⌝ₛ,⌜A⌝ₛ) ∧
  (∀ n ∈ ⌜c⌝ₛ, ∀ D ∈ ⌜P⌝ₛ, ⌜rd_entry0_m⌝ₚ(n,D,⌜F⌝ₛ) →
    ⌜gs_det_m⌝ₚ(⌜ω⌝ₛ,⌜B⌝ₛ,⌜T⌝ₛ,⌜E⌝ₛ,⌜V⌝ₛ,D))⟫
derive_free_closed jp_games_m

theorem jp_games_delta_l {d} (ω B T E V c P F A : Term d) : (jp_games_m ω B T E V c P F A).IsDelta0 :=
  .conj (fn0_delta_l ..) (.conj (.neg (gs_det_delta_l ..))
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (gs_det_delta_l ..)))))

theorem jp_games_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B T E V c P F A : Term d) :
    Formula.satisfies ρ (jp_games_m ω B T E V c P F A) ↔
      Jp_games_d (ω.eval ρ) (B.eval ρ) (T.eval ρ) (E.eval ρ) (V.eval ρ)
        (c.eval ρ) (P.eval ρ) (F.eval ρ) (A.eval ρ) := by
  simp only [jp_games_m,Jp_games_d,Formula.satisfies_conj_iff,fn0_sat_l hE,Formula.satisfies_neg_iff,
    gs_det_sat_l hE,Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

def Jp_check_d (φ : Formula 1 4) (ω S B T a c A E V P F t X η K D H W : M.Domain) : Prop :=
  Oc_square_d t X η K ∧ Rc_cert_d ja_op_s (ja_env_l S) D H W ∧ M.mem t D ∧ M.mem c η ∧
    Jp_local_d φ B a c A t X K H W ∧ Jp_table_d φ B a c P F t X K H W ∧ Jp_games_d ω B T E V c P F A

/-- 槽位依次为 ω、种子、实数族、局面、实数参数、代码、收益、
局面编号、偶数集合、表值域、收益图、方块边长、方块、序型、代码图、递归域、层图、递归界。 -/
def jp_check0_m (φ : Formula 1 4) : Formula 1 18 :=
  .conj (oc_square_m (.bound 11) (.bound 12) (.bound 13) (.bound 14))
    (.conj (ja_cert_m (.bound 1) (.bound 15) (.bound 16) (.bound 17))
      (.conj (.mem (.bound 11) (.bound 15)) (.conj (.mem (.bound 5) (.bound 13))
        (.conj (jp_local_m φ (.bound 2) (.bound 4) (.bound 5) (.bound 6) (.bound 11) (.bound 12) (.bound 14) (.bound 16) (.bound 17))
          (.conj (jp_table_m φ (.bound 2) (.bound 4) (.bound 5) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 14) (.bound 16) (.bound 17))
            (jp_games_m (.bound 0) (.bound 2) (.bound 3) (.bound 7) (.bound 8) (.bound 5) (.bound 9) (.bound 10) (.bound 6)))))))

theorem jp_check0_closed_l (φ : Formula 1 4) (hc : φ.FreeClosed) : (jp_check0_m φ).FreeClosed := by
  simp -implicitDefEqProofs [jp_check0_m,Definitional.Formula.FreeClosed,hc]

theorem jp_check0_delta_l (φ : Formula 1 4) : (jp_check0_m φ).IsDelta0 :=
  .conj (oc_square_delta_l ..) (.conj (ja_cert_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _)
    (.conj (jp_local_delta_l ..) (.conj (jp_table_delta_l ..) (jp_games_delta_l ..))))))

theorem jp_check0_sat_l (hKP : M.Models KP) (φ : Formula 1 4) (hc : φ.FreeClosed) (ρ : Env M 18) :
    Formula.satisfies ρ (jp_check0_m φ) ↔ Jp_check_d φ (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3)
      (ρ.bound 4) (ρ.bound 5) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10)
      (ρ.bound 11) (ρ.bound 12) (ρ.bound 13) (ρ.bound 14) (ρ.bound 15) (ρ.bound 16) (ρ.bound 17) := by
  simp only [jp_check0_m,Jp_check_d,Formula.satisfies_conj_iff,oc_square_sat_l hKP,ja_cert_sat_l hKP.1,
    Formula.satisfies_mem_iff,jp_local_sat_l hKP.1 φ hc,jp_table_sat_l hKP.1 φ hc,jp_games_sat_l hKP.1]
  rfl

/-- 从同一个最小坏收益实际构造代码方块、完整旧表与博弈矩阵。 -/
theorem Jp_min_d.check_l (hZF : M.Models ZF) {φ : Formula 1 4} (hcφ : φ.FreeClosed)
    {ω S B T a c A : M.Domain}
    (space : Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B)
    (finite : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T)
    (least : Jp_min_d (kp_pair_l (ZF.modelsKP hZF)) φ ω S B T a c)
    (present : Jp_d (kp_pair_l (ZF.modelsKP hZF)) φ S B a c A) :
    ∃ E V P F t X η K D H W, Gs_base_d ω B T E V ∧
      Gs_number_d (kp_pair_l (ZF.modelsKP hZF)) ω T E ∧
      Jp_check_d φ ω S B T a c A E V P F t X η K D H W := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have original := present
  obtain ⟨γ,q,Y,code,_⟩ := original
  obtain ⟨t,X,η,K,p,square,_,_,pc⟩ := oc_pair_square_l hZF code
  have hc : M.mem c η := (square.2.2.2.1.bound_l pc).2
  obtain ⟨D,H,W,cert,ht⟩ := ja_initial_certificate_l (ZF.models_kpi_l hZF) S t
  obtain ⟨P,F,table,all⟩ := least.table_l hZF hcφ space.1 square cert ht hc
  obtain ⟨A',define,negative⟩ := least.1
  have no : ¬ Det_d I ω B T A := (present.unique_l hZF define).symm ▸ negative
  obtain ⟨E,V,number,_,parity⟩ := gs_setup_l I hZF space.1 finite
  have index := number.function
  have games : Jp_games_d ω B T E V c P F A :=
    ⟨table.1,fun h => no ((gs_det_iff_l hZF space finite index parity).mpr h),
      fun _ _ _ _ edge => (gs_det_iff_l hZF space finite index parity).mp (all _ _ edge)⟩
  exact ⟨E,V,P,F,t,X,η,K,D,H,W,(gs_base_iff_l hZF space).mpr ⟨finite,index,parity⟩,number,
    square,cert,ht,hc,(jp_local_iff_l hZF square cert ht hc).mp present,table,games⟩

/-- 基础数据与有界代码矩阵共同恢复原收益、全局最小性及原非决定性。 -/
theorem Jp_check_d.sound_l (hZF : M.Models ZF) {φ : Formula 1 4} {ω S B T a c A E V P F t X η K D H W : M.Domain}
    (space : Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B) (base : Gs_base_d ω B T E V)
    (check : Jp_check_d φ ω S B T a c A E V P F t X η K D H W) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    Jp_d I φ S B a c A ∧ Jp_min_d I φ ω S B T a c ∧ ¬ Det_d I ω B T A := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨finite,index,parity⟩ := (gs_base_iff_l hZF space).mp base
  obtain ⟨square,cert,ht,hc,row,table,games⟩ := check
  have present := (jp_local_iff_l hZF square cert ht hc).mpr row
  have cover := table.cover_l hZF square cert ht hc
  have no : ¬ Det_d I ω B T A := fun h => games.2.1 ((gs_det_iff_l hZF space finite index parity).mp h)
  refine ⟨present,⟨⟨A,present,no⟩,?_⟩,no⟩
  rintro d hd ⟨A',code,negative⟩
  have edge := cover d hd A' code
  exact negative ((gs_det_iff_l hZF space finite index parity).mpr
    (games.2.2 d hd A' (games.1.bound_l edge).2 edge))

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 最小坏收益的完整博弈见证

同一实际初段收益表的每个值都决定，而指定收益不决定。策略量词已消为
实数量词，整个判断是一个 Δ₀ 矩阵，并实际放入包含全部实数的传递集合。
规范配对、Jensen 层和完整旧代码覆盖已全部进入同一有界矩阵。
同一结构见证记录成员同余、自然数识别、特殊实数、规范编号及有限解码闭包。
非传递见证坍塌后含全部背景实数，实数族准确识别为完整 Baire 空间；
原反例入口已选择二值实数参数，其固定性由同一规范化接口返回。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 前六槽为自然数配对方块、序型、编号图、零及两张特殊实数；其后保留原十八槽。 -/
def jp_witness_m (φ : Formula 1 4) : Formula 1 24 :=
  st_reals_m 6 3 4 5 0 1 2 (.conj (sr_space_m (.bound 6) (.bound 8))
    (.conj (rf_seed0_m (.bound 6) (.bound 8) (.bound 7))
      (.conj (gs_base_m (.bound 6) (.bound 8) (.bound 9) (.bound 13) (.bound 14))
        ((jp_check0_m φ).rename (fun i => i.succ.succ.succ.succ.succ.succ)))))

theorem jp_witness_closed_l {φ : Formula 1 4} (hc : φ.FreeClosed) : (jp_witness_m φ).FreeClosed :=
  st_reals_closed_l 6 3 4 5 0 1 2 ⟨sr_space_m_freeClosed _ _ rfl rfl,
    rf_seed0_m_freeClosed _ _ _ rfl rfl rfl,gs_base_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl,
    (Definitional.Formula.freeClosed_rename ..).mpr (jp_check0_closed_l φ hc)⟩

include hZF in
/-- 任意成员见证经规范化后给出背景中的实际代码、层和博弈矩阵。
这里保留实际坍塌图，恢复完整实数覆盖及实数族，并逐项固定所选二值参数。 -/
theorem jp_witness_read_l {φ : Formula 1 4} (hc : φ.FreeClosed)
    {ω z Q : M.Domain} {x : Fin 24 → M.Domain} (basis : Mc_nat_d ω z (x 4) (x 5))
    (cover : ∀ r, Fn0_d ω ω r → M.mem r Q)
    (hs : St_d Q (jp_witness_m φ) x) :
    ∃ U g, ∃ y : Fin 24 → M.Domain, M.TransitiveSet U ∧ Mc_map_d Q U g ∧ y 6 = ω ∧ y 3 = z ∧
      y 4 = x 4 ∧ y 5 = x 5 ∧ Oc_square_d ω (y 0) (y 1) (y 2) ∧
      (∀ r, Fn0_d ω ω r → M.mem r U) ∧ Lr_seed_d hZF ω (y 8) (y 7) ∧
      Fseq_space_d I ω ω (y 9) ∧
      (∀ r v, Bc_binary_d ω r → Rd_entry_d r v g → r = v) ∧
      (∀ i, Rd_entry_d (x i) (y i) g) ∧
      Jp_d I φ (y 7) (y 8) (y 10) (y 11) (y 12) ∧
      Jp_min_d I φ ω (y 7) (y 8) (y 9) (y 10) (y 11) ∧ ¬ Det_d I ω (y 8) (y 9) (y 12) ∧
      ∀ a b, Rd_entry_d a b g ↔ M.mem a Q ∧ Mc_value_d Q a b := by
  have closed : ((.conj (sr_space_m (.bound 6) (.bound 8))
      (.conj (rf_seed0_m (.bound 6) (.bound 8) (.bound 7))
        (.conj (gs_base_m (.bound 6) (.bound 8) (.bound 9) (.bound 13) (.bound 14))
          ((jp_check0_m φ).rename (fun i => i.succ.succ.succ.succ.succ.succ))))) : Formula 1 24).FreeClosed :=
    ⟨sr_space_m_freeClosed _ _ rfl rfl,rf_seed0_m_freeClosed _ _ _ rfl rfl rfl,
      gs_base_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl,
      (Definitional.Formula.freeClosed_rename ..).mpr (jp_check0_closed_l φ hc)⟩
  obtain ⟨U,g,y,ht,hg,ew,ez,ec,es,numbers,reals,binary,edges,truth,entry⟩ := st_reals_collapse_l hZF closed basis cover hs
  obtain ⟨hn,ν,values,truth⟩ := truth
  obtain ⟨nativeSpace,truth⟩ := (Formula.satisfies_conj_iff ..).mp truth
  obtain ⟨nativeSeed,truth⟩ := (Formula.satisfies_conj_iff ..).mp truth
  obtain ⟨nativeBase,truth⟩ := (Formula.satisfies_conj_iff ..).mp truth
  have nativeSpace := (sr_space_sat_l (rt_model_ext_l hZF.1 ht hn) ν (.bound 6) (.bound 8)).mp nativeSpace
  have rawSpace := (rt_reals_iff_l ht hn hZF.1 (ν.bound 6) (ν.bound 8)
    (fun r fr => reals r (by simpa only [values,ew] using fr))).mp nativeSpace
  have space : Baire_d I ω (y 8) := by
    refine ⟨basis.omega,fun r => ?_⟩
    have spec := rawSpace r
    change M.mem r (ν.bound 8).val ↔ Fn0_d (ν.bound 6).val (ν.bound 6).val r at spec
    rw [values 8,values 6,ew] at spec
    exact spec.trans ⟨fn0_function_l (ZF.modelsKP hZF),fn0_of_function_l (ZF.modelsKP hZF)⟩
  have shape := (rf_seed0_sat_l hZF.1 _ _ _ _).mp
    ((rt_model_delta_l ht hn (rf_seed0_delta_l ..) ν).mp nativeSeed)
  change Rf_seed0_d (ν.bound 6).val (ν.bound 8).val (ν.bound 7).val at shape
  rw [values 6,values 8,values 7,ew] at shape
  have seed : Lr_seed_d hZF ω (y 8) (y 7) := ⟨space,
    (rf_seed0_iff_l (ZF.modelsKP hZF) (basis.omega.transitive (ZF.modelsKP hZF))
      (fun r hr => fn0_of_function_l (ZF.modelsKP hZF) ((space.2 r).mp hr))
      ⟨x 4,(space.2 (x 4)).mpr (fn0_function_l (ZF.modelsKP hZF) basis.constant)⟩).mp shape⟩
  have base := (gs_base_sat_l hZF.1 _ _ _ _ _ _).mp
    ((rt_model_delta_l ht hn (gs_base_delta_l ..) ν).mp nativeBase)
  change Gs_base_d (ν.bound 6).val (ν.bound 8).val (ν.bound 9).val (ν.bound 13).val (ν.bound 14).val at base
  rw [values 6,values 8,values 9,values 13,values 14,ew] at base
  let ρ : Env M 18 := ⟨fun i => y i.succ.succ.succ.succ.succ.succ,fun _ => ω⟩
  have truth : St_d U (jp_check0_m φ) ρ.bound :=
    ⟨hn,Env.reindex ν (fun i => i.succ.succ.succ.succ.succ.succ),fun i => values i.succ.succ.succ.succ.succ.succ,
      (Formula.satisfies_rename ..).mp truth⟩
  have sat := (st_delta_l ht ⟨y 6,(hg.function.bound_l (edges 6)).2⟩ (jp_check0_m φ)
    (jp_check0_closed_l φ hc) (jp_check0_delta_l φ) ρ
      (fun i => (hg.function.bound_l (edges i.succ.succ.succ.succ.succ.succ)).2)).mp truth
  have check := (jp_check0_sat_l (ZF.modelsKP hZF) φ hc ρ).mp sat
  change Jp_check_d φ (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) (y 12) (y 13) (y 14)
    (y 15) (y 16) (y 17) (y 18) (y 19) (y 20) (y 21) (y 22) (y 23) at check
  rw [ew] at check
  obtain ⟨present,least,no⟩ := check.sound_l hZF space base
  exact ⟨U,g,y,ht,hg,ew,ez,ec,es,numbers,reals,seed,((gs_base_iff_l hZF space).mp base).1,binary,edges,present,least,no,entry⟩

def Jp_game_witness_d (φ : Formula 1 4)
    (ω S B T a c A : M.Domain) : Prop :=
  ∃ z c₀ s₀, Mc_nat_d ω z c₀ s₀ ∧ ∃ X₀ η₀ E₀ E V P F t X η K D H W Q,
    M.TransitiveSet Q ∧ (∀ x ∈ [X₀,η₀,E₀,z,c₀,s₀,ω,S,B,T,a,c,A,E,V,P,F,t,X,η,K,D,H,W], M.mem x Q) ∧
    St_d Q (jp_witness_m φ) (fun i => [X₀,η₀,E₀,z,c₀,s₀,ω,S,B,T,a,c,A,E,V,P,F,t,X,η,K,D,H,W].get i)

theorem Jp_min_d.game_witness_l {φ : Formula 1 4} (hcφ : φ.FreeClosed) {ω S B T a c A : M.Domain}
    (space : Baire_d I ω B) (finite : Fseq_space_d I ω ω T) (seed : Tc_d B S)
    (least : Jp_min_d I φ ω S B T a c) (present : Jp_d I φ S B a c A) :
    Jp_game_witness_d φ ω S B T a c A := by
  obtain ⟨E,V,P,F,t,X,η,K,D,H,W,base,_,check⟩ := least.check_l hZF hcφ space finite present
  obtain ⟨z,c₀,s₀,basis⟩ := mc_nat_exists_l (ZF.modelsKP hZF) space.1
  obtain ⟨X₀,product⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨η₀,E₀,numbers⟩ := oc_square_exists_l hZF (space.1.isOrdinal (ZF.modelsKP hZF)) product
  obtain ⟨Z,bound⟩ := kp_finite_cover_l (ZF.modelsKP hZF) [X₀,η₀,E₀,z,c₀,s₀,ω,S,B,T,a,c,A,E,V,P,F,t,X,η,K,D,H,W]
  obtain ⟨Q,tc⟩ := ZF.tc_exists_l I hZF Z
  have inside x (hx : x ∈ [X₀,η₀,E₀,z,c₀,s₀,ω,S,B,T,a,c,A,E,V,P,F,t,X,η,K,D,H,W]) : M.mem x Q :=
    tc.1 Z tc.2.1 x (bound x hx).2
  let ρ : Env M 18 := ⟨fun i => [ω,S,B,T,a,c,A,E,V,P,F,t,X,η,K,D,H,W].get i,fun _ => ω⟩
  have sat := (jp_check0_sat_l (ZF.modelsKP hZF) φ hcφ ρ).mpr check
  have hs := (st_delta_l tc.1 ⟨ω,inside ω (by simp)⟩ (jp_check0_m φ) (jp_check0_closed_l φ hcφ)
    (jp_check0_delta_l φ) ρ (fun i => inside _ (List.get_mem
      [X₀,η₀,E₀,z,c₀,s₀,ω,S,B,T,a,c,A,E,V,P,F,t,X,η,K,D,H,W] i.succ.succ.succ.succ.succ.succ))).mpr sat
  obtain ⟨hn,ν,values,hs⟩ := hs
  let δ := (((((ν.push ⟨s₀,inside s₀ (by simp)⟩).push ⟨c₀,inside c₀ (by simp)⟩).push
    ⟨z,inside z (by simp)⟩).push ⟨E₀,inside E₀ (by simp)⟩).push ⟨η₀,inside η₀ (by simp)⟩).push ⟨X₀,inside X₀ (by simp)⟩
  have reals r (fr : Fn0_d ω ω r) : M.mem r Q :=
    tc.1 B (inside B (by simp)) r ((space.2 r).mpr (fn0_function_l (ZF.modelsKP hZF) fr))
  refine ⟨z,c₀,s₀,basis,X₀,η₀,E₀,E,V,P,F,t,X,η,K,D,H,W,Q,tc.1,inside,
    (st_reals_transitive_l (ZF.modelsKP hZF) tc.1 basis numbers reals).mpr ⟨hn,δ,?_,?_⟩⟩
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl values)))))
  · apply (Formula.satisfies_conj_iff ..).mpr
    have dw : (δ.bound 6).val = ω := values 0
    have db : (δ.bound 8).val = B := values 2
    have ds : (δ.bound 7).val = S := values 1
    have dt : (δ.bound 9).val = T := values 3
    have de : (δ.bound 13).val = E := values 7
    have dv : (δ.bound 14).val = V := values 8
    have shape := (rf_seed0_iff_l (ZF.modelsKP hZF) (space.1.transitive (ZF.modelsKP hZF))
      (fun r hr => fn0_of_function_l (ZF.modelsKP hZF) ((space.2 r).mp hr))
      ⟨c₀,(space.2 c₀).mpr (fn0_function_l (ZF.modelsKP hZF) basis.constant)⟩).mpr seed
    have raw : Formula.satisfies (image_env_l (M := rt_model_l Q hn) (N := M) Subtype.val δ)
        (rf_seed0_m (.bound 6) (.bound 8) (.bound 7)) :=
      (rf_seed0_sat_l hZF.1 _ _ _ _).mpr (by
        change Rf_seed0_d (δ.bound 6).val (δ.bound 8).val (δ.bound 7).val
        simpa only [dw,db,ds] using shape)
    have nativeSeed := (rt_model_delta_l tc.1 hn (rf_seed0_delta_l ..) δ).mpr raw
    have rawBase : Formula.satisfies (image_env_l (M := rt_model_l Q hn) (N := M) Subtype.val δ)
        (gs_base_m (.bound 6) (.bound 8) (.bound 9) (.bound 13) (.bound 14)) :=
      (gs_base_sat_l hZF.1 _ _ _ _ _ _).mpr (by
        change Gs_base_d (δ.bound 6).val (δ.bound 8).val (δ.bound 9).val (δ.bound 13).val (δ.bound 14).val
        rw [dw,db,dt,de,dv]
        exact base)
    have nativeBase := (rt_model_delta_l tc.1 hn (gs_base_delta_l ..) δ).mpr rawBase
    refine ⟨(sr_space_sat_l (rt_model_ext_l hZF.1 tc.1 hn) δ (.bound 6) (.bound 8)).mpr ?_,
      (Formula.satisfies_conj_iff ..).mpr ⟨nativeSeed,
        (Formula.satisfies_conj_iff ..).mpr ⟨nativeBase,
          (Formula.satisfies_rename δ (fun i => i.succ.succ.succ.succ.succ.succ) (jp_check0_m φ)).mpr hs⟩⟩⟩
    apply (rt_reals_iff_l tc.1 hn hZF.1 (δ.bound 6) (δ.bound 8)
      (fun r fr => reals r (by simpa only [dw] using fr))).mpr
    intro r
    rw [dw,db]
    exact (space.2 r).trans ⟨fn0_of_function_l (ZF.modelsKP hZF),fn0_function_l (ZF.modelsKP hZF)⟩
end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 最小坏收益的仅实数参数见证

常零、后继及指定二值参数占三个自由槽。其余二十一个对象在成员见证内
存在量化；实数槽直接代入原矩阵，不用非外延结构中的定义等同替代字面参数。
构造和读回使用原 Sr_truth_d，见证允许非传递。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private def jp_real_slots_l (i : Fin 24) : Fin 24 :=
  ([0,1,2,3,21,22,4,5,6,7,23,8,9,10,11,12,13,14,15,16,17,18,19,20] : List (Fin 24)).get i

private def jp_real_aux_l (i : Fin 21) : Fin 24 :=
  ([0,1,2,3,6,7,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23] : List (Fin 24)).get i

def jp_real_m (φ : Formula 1 4) : Formula 1 3 :=
  rb_exists_m (n := 21) ((jp_witness_m φ).rename jp_real_slots_l)

theorem jp_real_closed_l {φ : Formula 1 4} (hc : φ.FreeClosed) : (jp_real_m φ).FreeClosed := by
  simp only [jp_real_m,rb_exists_closed_l,Definitional.Formula.freeClosed_rename]
  exact jp_witness_closed_l hc

theorem jp_real_sat_l (φ : Formula 1 4) (ρ : Env M 3) : Formula.satisfies ρ (jp_real_m φ) ↔
    ∃ x : Fin 24 → M.Domain, x 4 = ρ.bound 0 ∧ x 5 = ρ.bound 1 ∧ x 10 = ρ.bound 2 ∧
      Formula.satisfies (⟨x,ρ.free⟩ : Env M 24) (jp_witness_m φ) := by
  rw [jp_real_m,rb_exists_sat_l]
  constructor
  · rintro ⟨v,hs⟩
    let δ : Env M 24 := ⟨Fin.addCases (m := 21) (n := 3) (motive := fun _ => M.Domain) v ρ.bound,ρ.free⟩
    exact ⟨fun i => δ.bound (jp_real_slots_l i),rfl,rfl,rfl,
      (Formula.satisfies_rename δ jp_real_slots_l (jp_witness_m φ)).mp hs⟩
  · rintro ⟨x,hc,hs,ha,truth⟩
    let v : Fin 21 → M.Domain := fun i => x (jp_real_aux_l i)
    let δ : Env M 24 := ⟨Fin.addCases (m := 21) (n := 3) (motive := fun _ => M.Domain) v ρ.bound,ρ.free⟩
    have row : ∀ i : Fin 24, δ.bound (jp_real_slots_l i) = x i := by
      simp only [Fin.forall_fin_succ]
      exact ⟨rfl,rfl,rfl,rfl,hc.symm,hs.symm,rfl,rfl,rfl,rfl,ha.symm,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun i => Fin.elim0 i⟩
    have env : Env.reindex δ jp_real_slots_l = (⟨x,ρ.free⟩ : Env M 24) := by
      rw [Env.mk.injEq]
      exact ⟨funext row,rfl⟩
    refine ⟨v,(Formula.satisfies_rename δ jp_real_slots_l (jp_witness_m φ)).mpr ?_⟩
    exact env.symm ▸ truth

/-- 打包的三个实数参数与原二十四槽赋值逐项相同。 -/
theorem st_jp_real_l {Q : M.Domain} (φ : Formula 1 4) (r : Fin 3 → M.Domain) :
    St_d Q (jp_real_m φ) r ↔ ∃ x : Fin 24 → M.Domain,
      x 4 = r 0 ∧ x 5 = r 1 ∧ x 10 = r 2 ∧ St_d Q (jp_witness_m φ) x := by
  constructor
  · rintro ⟨hn,ρ,values,truth⟩
    obtain ⟨x,hc,hs,ha,sat⟩ := (jp_real_sat_l φ ρ).mp truth
    exact ⟨fun i => (x i).val,(congrArg Subtype.val hc).trans (values 0),
      (congrArg Subtype.val hs).trans (values 1),(congrArg Subtype.val ha).trans (values 2),hn,
      ⟨x,ρ.free⟩,fun _ => rfl,sat⟩
  · rintro ⟨x,hc,hs,ha,hn,ρ,values,truth⟩
    let δ : Env (rt_model_l Q hn) 3 :=
      ⟨Fin.cases (ρ.bound 4) (Fin.cases (ρ.bound 5) (fun _ => ρ.bound 10)),ρ.free⟩
    exact ⟨hn,δ,Fin.cases ((values 4).trans hc)
      (Fin.cases ((values 5).trans hs) (Fin.cases ((values 10).trans ha) (fun i => Fin.elim0 i))),
      (jp_real_sat_l φ δ).mpr ⟨ρ.bound,rfl,rfl,rfl,truth⟩⟩

theorem Jp_game_witness_d.real_l {φ : Formula 1 4} {ω S B T a c A : M.Domain}
    (space : Baire_d I ω B) (real : M.mem a B) (witness : Jp_game_witness_d φ ω S B T a c A) :
    ∃ z c₀ s₀, Mc_nat_d ω z c₀ s₀ ∧
      Sr_truth_d B (jp_real_m φ) (Fin.cases c₀ (Fin.cases s₀ (fun _ => a))) := by
  obtain ⟨z,c₀,s₀,basis,X₀,η₀,E₀,E,V,P,F,t,X,η,K,D,H,W,Q,trans,inside,truth⟩ := witness
  have rc := (space.2 c₀).mpr (fn0_function_l (ZF.modelsKP hZF) basis.constant)
  have rs := (space.2 s₀).mpr (fn0_function_l (ZF.modelsKP hZF) basis.successor)
  refine ⟨z,c₀,s₀,basis,Fin.cases rc (Fin.cases rs (Fin.cases real (fun i => Fin.elim0 i))),Q,
    fun r hr => trans B (inside B (by simp)) r hr,(st_jp_real_l φ _).mpr ?_⟩
  exact ⟨fun i => [X₀,η₀,E₀,z,c₀,s₀,ω,S,B,T,a,c,A,E,V,P,F,t,X,η,K,D,H,W].get i,rfl,rfl,rfl,truth⟩

/-- 原 8.3 意义的仅实数参数断言准确产生真实 L(ℝ) 种子上的最小坏收益。 -/
theorem jp_real_sound_l {φ : Formula 1 4} (hc : φ.FreeClosed) {ω B z c₀ s₀ a : M.Domain}
    (space : Baire_d I ω B) (basis : Mc_nat_d ω z c₀ s₀) (binary : Bc_binary_d ω a)
    (truth : Sr_truth_d B (jp_real_m φ) (Fin.cases c₀ (Fin.cases s₀ (fun _ => a)))) :
    ∃ S T c A, Lr_seed_d hZF ω B S ∧ Fseq_space_d I ω ω T ∧
      Jp_d I φ S B a c A ∧ Jp_min_d I φ ω S B T a c ∧ ¬ Det_d I ω B T A := by
  obtain ⟨_,Q,cover,sat⟩ := truth
  obtain ⟨x,ec,es,ea,sat⟩ := (st_jp_real_l φ _).mp sat
  change x 4 = c₀ at ec
  change x 5 = s₀ at es
  change x 10 = a at ea
  have source : Mc_nat_d ω z (x 4) (x 5) := by simpa only [ec,es] using basis
  obtain ⟨U,g,y,_,_,_,_,_,_,_,_,seed,finite,fixedBinary,edges,present,least,no,_⟩ :=
    jp_witness_read_l hZF hc source (fun r fr => cover r ((space.2 r).mpr (fn0_function_l (ZF.modelsKP hZF) fr))) sat
  have eb : y 8 = B := hZF.1.eq_of_same_members _ _ (fun r => (seed.1.2 r).trans (space.2 r).symm)
  have fixed : y 10 = a := (fixedBinary (x 10) (y 10) (by simpa only [ea] using binary) (edges 10)).symm.trans ea
  rw [eb,fixed] at present least
  rw [eb] at seed no
  exact ⟨y 7,y 9,y 11,y 12,seed,finite,present,least,no⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 最小坏收益的正负成员性实数见证

第四个自由实数是查询点的规范二值码。见证内实际解码原查询点，
并在同一最小坏收益上检查正负成员性。非传递见证的坍塌固定二值码，
规范解码唯一性再固定查询点；不要求任意原实数被坍塌逐点固定。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Jp_sign_d (p : Bool) (r A : M.Domain) : Prop := if p then M.mem r A else ¬ M.mem r A

/-- 前两槽是解码点及其二值码，余下二十四槽保持原见证顺序。 -/
def jp_point_m (p : Bool) : Formula 1 26 :=
  .conj (bc_graph_m (.bound 8) (.bound 2) (.bound 4) (.bound 1) (.bound 0))
    (if p then .mem (.bound 0) (.bound 14) else .neg (.mem (.bound 0) (.bound 14)))

theorem jp_point_closed_l (p : Bool) : (jp_point_m p).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [jp_point_m,Definitional.Formula.FreeClosed]

theorem jp_point_delta_l (p : Bool) : (jp_point_m p).IsDelta0 := by
  cases p
  · exact .conj (bc_graph_delta_l ..) (.neg (.mem _ _))
  · exact .conj (bc_graph_delta_l ..) (.mem _ _)

theorem jp_point_sat_l (hE : Extensional M) (p : Bool) (ρ : Env M 26) :
    Formula.satisfies ρ (jp_point_m p) ↔
      Bc_graph_d (ρ.bound 8) (ρ.bound 2) (ρ.bound 4) (ρ.bound 1) (ρ.bound 0) ∧
        Jp_sign_d p (ρ.bound 0) (ρ.bound 14) := by
  cases p <;> simp only [jp_point_m,Jp_sign_d,Bool.false_eq_true,↓reduceIte,
    Formula.satisfies_conj_iff,bc_graph_sat_l hE,Formula.satisfies_neg_iff,
    Formula.satisfies_mem_iff] <;> rfl

def jp_signed_witness_m (φ : Formula 1 4) (p : Bool) : Formula 1 26 :=
  .conj ((jp_witness_m φ).rename (fun i => i.succ.succ)) (jp_point_m p)

private def jp_signed_slots_l (i : Fin 26) : Fin 26 :=
  ([0,25,1,2,3,4,22,23,5,6,7,8,24,9,10,11,12,13,14,15,16,17,18,19,20,21] : List (Fin 26)).get i

private def jp_signed_aux_l (i : Fin 22) : Fin 26 :=
  ([0,2,3,4,5,8,9,10,11,13,14,15,16,17,18,19,20,21,22,23,24,25] : List (Fin 26)).get i

/-- 四个自由槽依次为常零、后继、收益参数及查询点二值码。 -/
def jp_signed_m (φ : Formula 1 4) (p : Bool) : Formula 1 4 :=
  rb_exists_m (n := 22) ((jp_signed_witness_m φ p).rename jp_signed_slots_l)

theorem jp_signed_closed_l {φ : Formula 1 4} (hc : φ.FreeClosed) (p : Bool) :
    (jp_signed_m φ p).FreeClosed := by
  simp only [jp_signed_m,rb_exists_closed_l,Definitional.Formula.freeClosed_rename]
  exact ⟨(Definitional.Formula.freeClosed_rename ..).mpr (jp_witness_closed_l hc),jp_point_closed_l p⟩

theorem jp_signed_sat_l (φ : Formula 1 4) (p : Bool) (ρ : Env M 4) :
    Formula.satisfies ρ (jp_signed_m φ p) ↔ ∃ x : Fin 26 → M.Domain,
      x 6 = ρ.bound 0 ∧ x 7 = ρ.bound 1 ∧ x 12 = ρ.bound 2 ∧ x 1 = ρ.bound 3 ∧
        Formula.satisfies (⟨x,ρ.free⟩ : Env M 26) (jp_signed_witness_m φ p) := by
  rw [jp_signed_m,rb_exists_sat_l]
  constructor
  · rintro ⟨v,hs⟩
    let δ : Env M 26 := ⟨Fin.addCases (m := 22) (n := 4) (motive := fun _ => M.Domain) v ρ.bound,ρ.free⟩
    exact ⟨fun i => δ.bound (jp_signed_slots_l i),rfl,rfl,rfl,rfl,
      (Formula.satisfies_rename δ jp_signed_slots_l (jp_signed_witness_m φ p)).mp hs⟩
  · rintro ⟨x,hc,hs,ha,hb,truth⟩
    let v : Fin 22 → M.Domain := fun i => x (jp_signed_aux_l i)
    let δ : Env M 26 := ⟨Fin.addCases (m := 22) (n := 4) (motive := fun _ => M.Domain) v ρ.bound,ρ.free⟩
    have row : ∀ i : Fin 26, δ.bound (jp_signed_slots_l i) = x i := by
      simp only [Fin.forall_fin_succ]
      exact ⟨rfl,hb.symm,rfl,rfl,rfl,rfl,hc.symm,hs.symm,rfl,rfl,rfl,rfl,ha.symm,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun i => Fin.elim0 i⟩
    have env : Env.reindex δ jp_signed_slots_l = (⟨x,ρ.free⟩ : Env M 26) := by
      rw [Env.mk.injEq]
      exact ⟨funext row,rfl⟩
    exact ⟨v,(Formula.satisfies_rename δ jp_signed_slots_l (jp_signed_witness_m φ p)).mpr (env.symm ▸ truth)⟩

theorem st_jp_signed_l {Q : M.Domain} (φ : Formula 1 4) (p : Bool) (r : Fin 4 → M.Domain) :
    St_d Q (jp_signed_m φ p) r ↔ ∃ x : Fin 26 → M.Domain,
      x 6 = r 0 ∧ x 7 = r 1 ∧ x 12 = r 2 ∧ x 1 = r 3 ∧ St_d Q (jp_signed_witness_m φ p) x := by
  constructor
  · rintro ⟨hn,ρ,values,truth⟩
    obtain ⟨x,hc,hs,ha,hb,sat⟩ := (jp_signed_sat_l φ p ρ).mp truth
    exact ⟨fun i => (x i).val,(congrArg Subtype.val hc).trans (values 0),
      (congrArg Subtype.val hs).trans (values 1),(congrArg Subtype.val ha).trans (values 2),
      (congrArg Subtype.val hb).trans (values 3),hn,⟨x,ρ.free⟩,fun _ => rfl,sat⟩
  · rintro ⟨x,hc,hs,ha,hb,hn,ρ,values,truth⟩
    let δ : Env (rt_model_l Q hn) 4 :=
      ⟨Fin.cases (ρ.bound 6) (Fin.cases (ρ.bound 7) (Fin.cases (ρ.bound 12) (fun _ => ρ.bound 1))),ρ.free⟩
    exact ⟨hn,δ,Fin.cases ((values 6).trans hc) (Fin.cases ((values 7).trans hs)
      (Fin.cases ((values 12).trans ha) (Fin.cases ((values 1).trans hb) (fun i => Fin.elim0 i)))),
      (jp_signed_sat_l φ p δ).mpr ⟨ρ.bound,rfl,rfl,rfl,rfl,truth⟩⟩

/-- 从任意原成员见证读出原查询点的正负成员性。解码与最小性使用同一坍塌图。 -/
theorem jp_signed_sound_l {φ : Formula 1 4} (hc : φ.FreeClosed) {ω B z c₀ s₀ a b r : M.Domain}
    (space : Baire_d I ω B) (basis : Mc_nat_d ω z c₀ s₀) (ba : Bc_binary_d ω a)
    (bb : Bc_binary_d ω b) (read : Bc_read_d I ω b r) (p : Bool)
    (truth : Sr_truth_d B (jp_signed_m φ p) (fun i => [c₀,s₀,a,b].get i)) :
    ∃ S T c A, Lr_seed_d hZF ω B S ∧ Fseq_space_d I ω ω T ∧
      Jp_d I φ S B a c A ∧ Jp_min_d I φ ω S B T a c ∧ ¬ Det_d I ω B T A ∧ Jp_sign_d p r A := by
  obtain ⟨_,Q,cover,sat⟩ := truth
  obtain ⟨x,ec,es,ea,eb,hn,ρ,values,sat⟩ := (st_jp_signed_l φ p _).mp sat
  change x 6 = c₀ at ec
  change x 7 = s₀ at es
  change x 12 = a at ea
  change x 1 = b at eb
  obtain ⟨base,point⟩ := (Formula.satisfies_conj_iff ρ _ _).mp sat
  have base : St_d Q (jp_witness_m φ) (fun i => x i.succ.succ) :=
    ⟨hn,Env.reindex ρ (fun i => i.succ.succ),fun i => values i.succ.succ,
      (Formula.satisfies_rename ρ (fun i => i.succ.succ) (jp_witness_m φ)).mp base⟩
  have source : Mc_nat_d ω z (x 6) (x 7) := by simpa only [ec,es] using basis
  obtain ⟨U,g,y,ht,hg,ew,_,_,_,square,_,seed,finite,binary,edges,present,least,no,_⟩ :=
    jp_witness_read_l hZF hc source
      (fun t ft => cover t ((space.2 t).mpr (fn0_function_l (ZF.modelsKP hZF) ft))) base
  obtain ⟨v,ev,point⟩ := st_map_l hg (jp_point_closed_l p) (show St_d Q (jp_point_m p) x from ⟨hn,ρ,values,point⟩)
  have same (i : Fin 24) : v i.succ.succ = y i :=
    hg.function.2.2 _ (hg.function.bound_l (ev i.succ.succ)).1 _
      (hg.function.bound_l (ev i.succ.succ)).2 _ (hg.function.bound_l (edges i)).2 (ev i.succ.succ) (edges i)
  have fixedB : v 1 = b := (binary (x 1) (v 1) (by simpa only [eb] using bb) (ev 1)).symm.trans eb
  let δ : Env M 26 := ⟨v,fun _ => ω⟩
  have raw := (st_delta_l ht ⟨v 8,(hg.function.bound_l (ev 8)).2⟩ (jp_point_m p)
    (jp_point_closed_l p) (jp_point_delta_l p) δ (fun i => (hg.function.bound_l (ev i)).2)).mp point
  obtain ⟨graph,sign⟩ := (jp_point_sat_l hZF.1 p δ).mp raw
  change Bc_graph_d (v 8) (v 2) (v 4) (v 1) (v 0) at graph
  change Jp_sign_d p (v 0) (v 14) at sign
  have eω : v 8 = y 6 := same 6
  have eX : v 2 = y 0 := same 0
  have eE : v 4 = y 2 := same 2
  have eA : v 14 = y 12 := same 12
  rw [eω,eX,eE,ew,fixedB] at graph
  have decoded : v 0 = r := bc_read_unique_l (ZF.modelsKP hZF) ((bc_graph_read_l hZF square).mp graph) read
  rw [decoded,eA] at sign
  have realSpace : y 8 = B := hZF.1.eq_of_same_members _ _ (fun t => (seed.1.2 t).trans (space.2 t).symm)
  have fixedA : y 10 = a := (binary (x 12) (y 10) (by simpa only [ea] using ba) (edges 10)).symm.trans ea
  rw [realSpace,fixedA] at present least
  rw [realSpace] at seed no
  exact ⟨y 7,y 9,y 11,y 12,seed,finite,present,least,no,sign⟩

/-- 同一个实际传递见证、同一组三个固定参数同时服务所有查询点和两种符号。 -/
theorem Jp_game_witness_d.signed_l {φ : Formula 1 4} {ω S B T a c A : M.Domain}
    (space : Baire_d I ω B) (real : M.mem a B) (witness : Jp_game_witness_d φ ω S B T a c A) :
    ∃ z c₀ s₀, Mc_nat_d ω z c₀ s₀ ∧ ∀ b r, Bc_binary_d ω b → Bc_read_d I ω b r →
      ∀ p, Jp_sign_d p r A → Sr_truth_d B (jp_signed_m φ p) (fun i => [c₀,s₀,a,b].get i) := by
  obtain ⟨z,c₀,s₀,basis,X₀,η₀,E₀,E,V,P,F,t,X,η,K,D,H,W,Q,trans,inside,truth⟩ := witness
  have square : Oc_square_d ω X₀ η₀ E₀ := st_reals_square_l (ZF.modelsKP hZF) trans truth
  have rc := (space.2 c₀).mpr (fn0_function_l (ZF.modelsKP hZF) basis.constant)
  have rs := (space.2 s₀).mpr (fn0_function_l (ZF.modelsKP hZF) basis.successor)
  have cover : M.MemberSubset B Q := fun r hr => trans B (inside B (by simp)) r hr
  refine ⟨z,c₀,s₀,basis,fun b r bb read p sign => ?_⟩
  have rb := (space.2 b).mpr (fn0_function_l (ZF.modelsKP hZF) bb.1)
  have rr := (space.2 r).mpr (fn0_function_l (ZF.modelsKP hZF) read.1)
  have graph := (bc_graph_read_l hZF square).mpr read
  obtain ⟨hn,ρ,values,truth⟩ := truth
  let δ := (ρ.push ⟨b,cover b rb⟩).push ⟨r,cover r rr⟩
  have raw : Formula.satisfies (image_env_l (M := rt_model_l Q hn) (N := M) Subtype.val δ) (jp_point_m p) := by
    apply (jp_point_sat_l hZF.1 p _).mpr
    change Bc_graph_d (ρ.bound 6).val (ρ.bound 0).val (ρ.bound 2).val b r ∧ Jp_sign_d p r (ρ.bound 12).val
    simp only [values]
    exact ⟨graph,sign⟩
  have point := (rt_model_delta_l trans hn (jp_point_delta_l p) δ).mpr raw
  have sat : Formula.satisfies δ (jp_signed_witness_m φ p) :=
    (Formula.satisfies_conj_iff δ _ _).mpr
      ⟨(Formula.satisfies_rename δ (fun i => i.succ.succ) (jp_witness_m φ)).mpr truth,point⟩
  refine ⟨?_,Q,cover,(st_jp_signed_l φ p _).mpr
    ⟨fun i => (δ.bound i).val,values 4,values 5,values 10,rfl,hn,δ,fun _ => rfl,sat⟩⟩
  exact Fin.cases rc (Fin.cases rs (Fin.cases real (Fin.cases rb (fun i => Fin.elim0 i))))

/-- 正负断言均准确刻画原最小坏收益上的成员性，查询点仍是原 Baire 实数。 -/
theorem Jp_min_d.signed_real_l {φ : Formula 1 4} (hc : φ.FreeClosed) {ω S B T a c A : M.Domain}
    (space : Baire_d I ω B) (finite : Fseq_space_d I ω ω T) (seed : Tc_d B S)
    (ba : Bc_binary_d ω a) (least : Jp_min_d I φ ω S B T a c) (present : Jp_d I φ S B a c A) :
    ∃ z c₀ s₀, Mc_nat_d ω z c₀ s₀ ∧ ∀ b r, Bc_binary_d ω b → Bc_read_d I ω b r → ∀ p,
      Sr_truth_d B (jp_signed_m φ p) (fun i => [c₀,s₀,a,b].get i) ↔ Jp_sign_d p r A := by
  obtain ⟨z,c₀,s₀,basis,complete⟩ := (least.game_witness_l hZF hc space finite seed present).signed_l hZF space
    ((space.2 a).mpr (fn0_function_l (ZF.modelsKP hZF) ba.1))
  refine ⟨z,c₀,s₀,basis,fun b r bb read p => ⟨fun truth => ?_,complete b r bb read p⟩⟩
  obtain ⟨S',T',d,D,seed',finite',present',least',_,sign⟩ := jp_signed_sound_l hZF hc space basis ba bb read p truth
  exact (least'.same_payoff_l hZF seed'.2 seed finite' finite least present' present).2 ▸ sign

/-- 原 AD 否定直接生产真实 L(ℝ) 内的最小坏收益，并对每个原对局实数
实际构造二值码及两个准确互补的 Σ₁(ℝ) 断言。常零、后继和收益参数统一固定。 -/
theorem lr_min_counterexample_l (bad : ¬ M.SatisfiesSentence Axioms.lr_ad) :
    ∃ ω B S, ∃ seed : Lr_seed_d hZF ω B S,
      let D := la_model_l S (ZF.models_kpi_l hZF)
      let hD := la_model_zf_l S hZF seed.2.1
      let J := kp_pair_l (ZF.modelsKP hD)
      ∃ w b s T a c A : D.Domain, w.val = ω ∧ b.val = B ∧ s.val = S ∧
        Lr_seed_d hD w b s ∧ Fseq_space_d J w w T ∧ D.mem a b ∧ Bc_binary_d w a ∧
        Jp_min_d J lr_payoff_m w s b T a c ∧ Jp_d J lr_payoff_m s b a c A ∧ ¬ Det_d J w b T A ∧
        ∃ z c₀ s₀, Mc_nat_d w z c₀ s₀ ∧ ∀ x, D.mem x b →
          ∃ e, Bc_binary_d w e ∧ Bc_read_d J w e x ∧ ∀ p,
            Sr_truth_d b (jp_signed_m lr_payoff_m p) (fun i => [c₀,s₀,a,e].get i) ↔ Jp_sign_d p x A := by
  obtain ⟨ω,B,S,seed⟩ := lr_seed_exists_l hZF
  let D := la_model_l S (ZF.models_kpi_l hZF)
  have hD : D.Models ZF := la_model_zf_l S hZF seed.2.1
  let J := kp_pair_l (ZF.modelsKP hD)
  obtain ⟨w,b,s,ew,eb,es,native,self⟩ := la_real_self_l hZF seed.1.1 seed.2
    (fun x _ => (Iff.intro (fn0_function_l (ZF.modelsKP hZF)) (fn0_of_function_l (ZF.modelsKP hZF))).trans (seed.1.2 x).symm)
  obtain ⟨T,space⟩ := ZF.fseq_space_exists_l J hD native.1.1 w
  have counter : ∃ A : D.Domain, D.MemberSubset A b ∧ ¬ Det_d J w b T A := by
    apply Classical.byContradiction
    intro none
    apply bad
    apply lr_ad_of_seed_det_l hZF seed native.1 space
    intro A sub
    exact Classical.byContradiction (fun no => none ⟨A,sub,no⟩)
  obtain ⟨A,sub,no⟩ := counter
  let A' : (la_model_l s (ZF.models_kpi_l hD)).Domain := ⟨A,self A⟩
  obtain ⟨a,c,C,real,binary,least,present,negative,_⟩ := jp_min_payoff_l hD native A' sub no
  obtain ⟨z,c₀,s₀,basis,signs⟩ := least.signed_real_l hD lr_payoff_closed_l native.1 space native.2 binary present
  refine ⟨ω,B,S,seed,w,b,s,T,a,c,C,ew,eb,es,native,space,real,binary,least,present,negative,
    z,c₀,s₀,basis,fun x hx => ?_⟩
  obtain ⟨e,be,read⟩ := bc_encode_l hD native.1.1 (fn0_of_function_l (ZF.modelsKP hD) ((native.1.2 x).mp hx))
  exact ⟨e,be,read,signs e x be read⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 原 L(ℝ) 反例的实际有界数据

固定二值参数、真实种子、博弈基础及原最小坏收益矩阵共用十八个槽位。
整个证书为 Δ₀，因而可进入弱测试壳；其中没有测试模型 ZF 或全实数
绝对性的额外假设。实际来源仍是规范 lr_ad 的否定。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}}

structure Jp_counter_d (φ : Formula 1 4) (v : Fin 18 → M.Domain) : Prop where
  binary : Bc_binary_d (v 0) (v 4)
  seed : Rf_seed0_d (v 0) (v 2) (v 1)
  base : Gs_base_d (v 0) (v 2) (v 3) (v 7) (v 8)
  check : Jp_check_d φ (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)
    (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16) (v 17)

def jp_counter_m (φ : Formula 1 4) : Formula 1 18 :=
  .conj (bc_binary_m (.bound 0) (.bound 4))
    (.conj (rf_seed0_m (.bound 0) (.bound 2) (.bound 1))
      (.conj (gs_base_m (.bound 0) (.bound 2) (.bound 3) (.bound 7) (.bound 8)) (jp_check0_m φ)))

theorem jp_counter_closed_l {φ : Formula 1 4} (hc : φ.FreeClosed) : (jp_counter_m φ).FreeClosed :=
  ⟨by simp -implicitDefEqProofs,by simp -implicitDefEqProofs,
    by simp -implicitDefEqProofs,jp_check0_closed_l φ hc⟩

theorem jp_counter_delta_l (φ : Formula 1 4) : (jp_counter_m φ).IsDelta0 :=
  .conj (bc_binary_delta_l ..) (.conj (rf_seed0_delta_l ..) (.conj (gs_base_delta_l ..) (jp_check0_delta_l φ)))

theorem jp_counter_sat_l (hKP : M.Models KP) {φ : Formula 1 4} (hc : φ.FreeClosed) (ρ : Env M 18) :
    Formula.satisfies ρ (jp_counter_m φ) ↔ Jp_counter_d φ ρ.bound := by
  simp only [jp_counter_m,Formula.satisfies_conj_iff,bc_binary_sat_l hKP.1,rf_seed0_sat_l hKP.1,
    gs_base_sat_l hKP.1,jp_check0_sat_l hKP φ hc]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,fun h => ⟨h.binary,h.seed,h.base,h.check⟩⟩

/-- 原反例的证书先在真实 L(ℝ) 内构造，再沿传递包含搬到背景。 -/
theorem lr_counterexample_data_l (hZF : M.Models ZF) (bad : ¬ M.SatisfiesSentence Axioms.lr_ad) :
    ∃ v : Fin 18 → M.Domain, Lr_seed_d hZF (v 0) (v 2) (v 1) ∧ Jp_counter_d lr_payoff_m v ∧
      Gs_number_d (kp_pair_l (ZF.modelsKP hZF)) (v 0) (v 3) (v 7) := by
  obtain ⟨ω,B,S,seed,w,b,s,T,a,c,A,ew,eb,es,native,finite,_,binary,least,present,_⟩ :=
    lr_min_counterexample_l hZF bad
  let D := la_model_l S (ZF.models_kpi_l hZF)
  have hD : D.Models ZF := la_model_zf_l S hZF seed.2.1
  obtain ⟨E,V,P,F,t,X,η,K,C,H,W,base,number,check⟩ :=
    least.check_l hD lr_payoff_closed_l native.1 finite present
  let v : Fin 18 → D.Domain := fun i => [w,s,b,T,a,c,A,E,V,P,F,t,X,η,K,C,H,W].get i
  have shape := (rf_seed0_iff_l (ZF.modelsKP hD) (native.1.1.transitive (ZF.modelsKP hD))
    (fun r hr => fn0_of_function_l (ZF.modelsKP hD) ((native.1.2 r).mp hr))
    ⟨a,(native.1.2 a).mpr (fn0_function_l (ZF.modelsKP hD) binary.1)⟩).mpr native.2
  let ρ : Env D 18 := ⟨v,fun _ => w⟩
  have sat := (jp_counter_sat_l (ZF.modelsKP hD) lr_payoff_closed_l ρ).mpr ⟨binary,shape,base,check⟩
  have transferred := (la_model_delta_l S (ZF.models_kpi_l hZF) seed.2.1 (jp_counter_delta_l lr_payoff_m) ρ).mp sat
  have data := (jp_counter_sat_l (ZF.modelsKP hZF) lr_payoff_closed_l _).mp transferred
  have full : ∀ t x, M.mem x t.val ↔ ∃ u : D.Domain, D.mem u t ∧ u.val = x :=
    fun t x => ⟨fun hx => ⟨⟨x,la_transitive_l S (ZF.models_kpi_l hZF) seed.2.1 t.property hx⟩,hx,rfl⟩,
      fun ⟨u,hu,eq⟩ => eq ▸ hu⟩
  have number' := number.image_l hD hZF (Subtype.val : D.Domain → M.Domain)
    (fun _ _ eq => Subtype.ext eq) full native.1.1
  refine ⟨fun i => (v i).val,?_,data,number'⟩
  change Lr_seed_d hZF w.val b.val s.val
  rw [ew,eb,es]
  exact seed

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 原查询实数的派生正负断言

二值码与规范常零、后继图在断言内部实际存在量化，唯一自由实数仍是
指定收益参数和原查询点。派生模型中的同一个最小坏代码为每个查询提供一侧见证。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Dq_signed_d (φ : Formula 1 4) (p : Bool) (B ω a x : M.Domain) : Prop := ∃ z c s b,
  Mc_nat_d ω z c s ∧ Bc_binary_d ω a ∧ Bc_binary_d ω b ∧ Bc_read_d I ω b x ∧
    Dr_truth_d B (jp_signed_m φ p) (fun i => [c,s,a,b].get i)

def dq_signed_m (φ : Formula 1 4) (p : Bool) : Formula 1 4 := .existsE (.existsE (.existsE (.existsE
  (.conj (mc_nat_m (.bound 5) (.bound 3) (.bound 2) (.bound 1))
    (.conj (bc_binary_m (.bound 5) (.bound 6)) (.conj (bc_binary_m (.bound 5) (.bound 0))
      (.conj (bc_read_m (.bound 5) (.bound 0) (.bound 7))
        (dr_m (jp_signed_m φ p) (.bound 4) (fun i => [.bound 2,.bound 1,.bound 6,.bound 0].get i)))))))))

theorem dq_signed_closed_l {φ : Formula 1 4} (hc : φ.FreeClosed) (p : Bool) : (dq_signed_m φ p).FreeClosed := by
  simp only [dq_signed_m,Definitional.Formula.FreeClosed]
  refine ⟨by simp -implicitDefEqProofs,by simp -implicitDefEqProofs,by simp -implicitDefEqProofs,
    by simp -implicitDefEqProofs,dr_closed_l _ (jp_signed_closed_l hc p) _ _ rfl ?_⟩
  simp only [Fin.forall_fin_succ]
  exact ⟨rfl,rfl,rfl,rfl,fun i => Fin.elim0 i⟩

theorem dq_signed_sat_l (hKP : M.Models KP) {φ : Formula 1 4} (hc : φ.FreeClosed) (p : Bool) (ρ : Env M 4) :
    Formula.satisfies ρ (dq_signed_m φ p) ↔ Dq_signed_d I φ p (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) := by
  simp only [dq_signed_m,Dq_signed_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    mc_nat_sat_l hKP.1,bc_binary_sat_l hKP.1,bc_read_sat_l I hKP.1,dr_sat_l hKP _ (jp_signed_closed_l hc p)]
  apply exists_congr; intro z
  apply exists_congr; intro c
  apply exists_congr; intro s
  apply exists_congr; intro b
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply iff_of_eq
  apply congrArg (Dr_truth_d (ρ.bound 0) (jp_signed_m φ p))
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

/-- 原 8.5 上传的实际见证：背景解码固定原查询点，带符号断言在真实 L(ℝ) 内成立。 -/
def Lq_signed_d (φ : Formula 1 4) (p : Bool) (ω a x : M.Domain) : Prop :=
  ∃ B, Baire_d J ω B ∧ ∃ z c s b,
    Mc_nat_d ω z c s ∧ Bc_binary_d ω a ∧ Bc_binary_d ω b ∧ Bc_read_d J ω b x ∧
    ∃ b₀ : (InnerModel.Relative.lr_model_l hZF).Domain, b₀.val = B ∧
    ∃ v : Fin 4 → (InnerModel.Relative.lr_model_l hZF).Domain,
      (∀ i, (v i).val = ([c,s,a,b] : List M.Domain).get i) ∧ Sr_truth_d b₀ (jp_signed_m φ p) v

/-- 一个实际最小坏代码同时覆盖所有原查询；二值码在同一派生模型内构造。 -/
theorem Dm_min_d.signed_queries_l {φ : Formula 1 4} (hc : φ.FreeClosed) {ω B a c : M.Domain}
    (hw : M.IsOmega ω) (ba : Bc_binary_d ω a) (least : Dm_min_d hZF φ B a c) :
    ∀ x, M.mem x B → Dq_signed_d J φ true B ω a x ∨ Dq_signed_d J φ false B ω a x := by
  obtain ⟨S,tc,b,a₀,c₀,eb,ea,_,_,w,U,T,space,seed,finite,minimum⟩ := least
  let D := la_model_l S (ZF.models_kpi_l hZF)
  have hD := la_model_zf_l S hZF tc.1
  let K := kp_pair_l (ZF.modelsKP hD)
  let ω₀ : D.Domain := ⟨ω,la_ordinal_l S (ZF.models_kpi_l hZF) tc.1 (hw.isOrdinal (ZF.modelsKP hZF))⟩
  have hw₀ : D.IsOmega ω₀ := la_omega_l S hZF tc.1 hw
  have ew : w.val = ω := congrArg Subtype.val (hD.1.eq_of_same_members w ω₀
    (fun i => ⟨space.1.2 ω₀ hw₀.1 i,hw₀.2 w space.1.1 i⟩))
  have inj : Function.Injective (Subtype.val : D.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full (t : D.Domain) (y : M.Domain) : M.mem y t.val ↔ ∃ z : D.Domain, D.mem z t ∧ z.val = y :=
    ⟨fun h => ⟨⟨y,la_transitive_l S (ZF.models_kpi_l hZF) tc.1 t.property h⟩,h,rfl⟩,fun ⟨_,h,eq⟩ => eq ▸ h⟩
  have binary : Bc_binary_d w a₀ := (bc_binary_image_l Subtype.val inj full hD.1 hZF.1).mpr (by simpa only [ew,ea] using ba)
  obtain ⟨A,present,_⟩ := minimum.1
  obtain ⟨z,zero,succ,basis,signs⟩ := minimum.signed_real_l hD hc space finite seed binary present
  have natural : Mc_nat_d ω z.val zero.val succ.val := by
    have moved := basis.image_l hD.1 hZF.1 Subtype.val inj full (show M.IsOmega w.val from ew.symm ▸ hw)
    simpa only [ew] using moved
  intro x hx
  let r : D.Domain := ⟨x,la_transitive_l S (ZF.models_kpi_l hZF) tc.1 b.property (eb.symm ▸ hx)⟩
  have hr : D.mem r b := by
    change M.mem x b.val
    exact eb.symm ▸ hx
  obtain ⟨code,bits,read⟩ := bc_encode_l hD space.1 (fn0_of_function_l (ZF.modelsKP hD) ((space.2 r).mp hr))
  have bitsM : Bc_binary_d ω code.val := ew ▸ (bc_binary_image_l Subtype.val inj full hD.1 hZF.1).mp bits
  have readM : Bc_read_d J ω code.val x := ew ▸ (bc_read_image_l Subtype.val inj full hD hZF (space.1.isOrdinal (ZF.modelsKP hD))).mp read
  have make p (sign : Jp_sign_d p r A) : Dq_signed_d J φ p B ω a x := by
    have truth := (signs code r bits read p).mpr sign
    refine ⟨z.val,zero.val,succ.val,code.val,natural,ba,bitsM,readM,?_⟩
    apply (dr_model_l (ZF.models_kpi_l hZF) tc (jp_signed_m φ p) (jp_signed_closed_l hc p) _).mpr
    refine ⟨b,eb,(fun i => [zero,succ,a₀,code].get i),?_,truth⟩
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases ea (Fin.cases rfl (fun i => Fin.elim0 i))))
  classical
  by_cases sign : D.mem r A
  · exact Or.inl (make true sign)
  · exact Or.inr (make false sign)

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 上传的正负查询指向同一个实际 L(ℝ) 收益

包含映射的成员满性反射自然数基、二值码和解码图，再在 L(ℝ) 内调用
原带符号见证的声音性。两侧允许不同的基与查询码；最小代码唯一性
直接识别收益，不把任意集合模型的真值当成绝对真值。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

/-- 解码原 8.5 的实际输出；收益、最小性及符号均在真实 L(ℝ) 内解释。 -/
theorem Lq_signed_d.native_l {φ : Formula 1 4} (hc : φ.FreeClosed) {p : Bool} {ω a x : M.Domain}
    (query : Lq_signed_d hZF φ p ω a x) :
    let L := lr_model_l hZF
    let hL := lr_model_zf_l hZF
    let J := kp_pair_l (ZF.modelsKP hL)
    ∃ w b a' x' S T c A : L.Domain,
      w.val = ω ∧ a'.val = a ∧ x'.val = x ∧
      Baire_d (kp_pair_l (ZF.modelsKP hZF)) w.val b.val ∧
      Lr_seed_d hL w b S ∧ Fseq_space_d J w w T ∧
      Jp_d J φ S b a' c A ∧ Jp_min_d J φ w S b T a' c ∧
      ¬ Det_d J w b T A ∧ Jp_sign_d p x' A := by
  obtain ⟨B,space,z,c,s,code,basis,ba,bb,read,b,eb,v,images,truth⟩ := query
  let L := lr_model_l hZF
  have hL : L.Models ZF := lr_model_zf_l hZF
  let J := kp_pair_l (ZF.modelsKP hL)
  have ec : (v 0).val = c := images 0
  have es : (v 1).val = s := images 1
  have ea : (v 2).val = a := images 2
  have eb' : (v 3).val = code := images 3
  have inj : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full (t : L.Domain) (y : M.Domain) : M.mem y t.val ↔ ∃ r : L.Domain, L.mem r t ∧ r.val = y :=
    ⟨fun hy => ⟨⟨y,lr_transitive_l hZF t.property hy⟩,hy,rfl⟩,fun ⟨_,hy,eq⟩ => eq ▸ hy⟩
  let w : L.Domain := ⟨ω,lr_ordinal_l hZF (space.1.isOrdinal (ZF.modelsKP hZF))⟩
  have hw : L.IsOmega w := by
    obtain ⟨u,hu⟩ := ZF.exists_omega hL
    have moved := image_omega_l (hEN := hZF.1) Subtype.val inj full hL
      (fun _ => KP.mem_minimal_exists_d (ZF.modelsKP hZF)) hu
      (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D u.val)
    have eq : u.val = ω := hZF.1.eq_of_same_members _ _
      (fun t => ⟨moved.2 ω space.1.1 t,space.1.2 u.val moved.1 t⟩)
    exact (show u = w from Subtype.ext eq) ▸ hu
  have fn (r : L.Domain) : Fn0_d w w r ↔ Fn0_d ω ω r.val := by
    let ρ : Env L 3 := ⟨fun i => [w,w,r].get i,fun _ => w⟩
    exact (fn0_sat_l hL.1 ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      ((delta0_image_l Subtype.val inj full (fn0_delta_l ..) ρ).trans (fn0_sat_l hZF.1 _ _ _ _))
  have native : Baire_d J w b := by
    refine ⟨hw,fun r => ?_⟩
    change M.mem r.val b.val ↔ L.IsSetFunctionFromTo J r w w
    rw [eb,space.2]
    exact (Iff.intro (fn0_of_function_l (ZF.modelsKP hZF)) (fn0_function_l (ZF.modelsKP hZF))).trans
      ((fn r).symm.trans (Iff.intro (fn0_function_l (ZF.modelsKP hL)) (fn0_of_function_l (ZF.modelsKP hL))))
  let x' : L.Domain := ⟨x,lr_real_l hZF space ((space.2 x).mpr (fn0_function_l (ZF.modelsKP hZF) read.1))⟩
  obtain ⟨i,_,hi⟩ := space.1.1.1
  have hz : M.mem z ω := (basis.constant.bound_l ((basis.constant_entry i z).mpr ⟨hi,rfl⟩)).2
  let z' : L.Domain := ⟨z,lr_transitive_l hZF w.property hz⟩
  have natural : Mc_nat_d w z' (v 0) (v 1) := by
    let ρ : Env L 4 := ⟨fun i => [w,z',v 0,v 1].get i,fun _ => w⟩
    apply (mc_basis_iff_l hL.1 hw).mp
    apply (mc_basis_sat_l hL.1 ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3)).mp
    apply (delta0_image_l Subtype.val inj full (mc_basis_delta_l ..) ρ).mpr
    apply (mc_basis_sat_l hZF.1 (image_env_l Subtype.val ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3)).mpr
    change Mc_basis_d ω z (v 0).val (v 1).val
    simpa only [ec,es] using (mc_basis_iff_l hZF.1 space.1).mpr basis
  have binaryA : Bc_binary_d w (v 2) :=
    (bc_binary_image_l Subtype.val inj full hL.1 hZF.1).mpr (by simpa only [ea] using ba)
  have binary : Bc_binary_d w (v 3) :=
    (bc_binary_image_l Subtype.val inj full hL.1 hZF.1).mpr (by simpa only [eb'] using bb)
  have decoded : Bc_read_d J w (v 3) x' :=
    (bc_read_image_l Subtype.val inj full hL hZF (hw.isOrdinal (ZF.modelsKP hL))).mpr
      (by simpa only [eb'] using read)
  have row : (fun i => ([v 0,v 1,v 2,v 3] : List L.Domain).get i) = v :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  obtain ⟨S,T,d,A,seed,finite,present,least,no,sign⟩ :=
    jp_signed_sound_l hL hc native natural binaryA binary decoded p (row.symm ▸ truth)
  exact ⟨w,b,v 2,x',S,T,d,A,rfl,images 2,rfl,eb.symm ▸ space,seed,finite,present,least,no,sign⟩

/-- 任意上传见证均指向指定参数的实际最小坏收益，无须统一各次的二值码。 -/
theorem Lq_signed_d.sign_l {φ : Formula 1 4} (hc : φ.FreeClosed) {p : Bool}
    {w b a x S T c A : (InnerModel.Relative.lr_model_l hZF).Domain}
    (seed : Lr_seed_d (lr_model_zf_l hZF) w b S)
    (finite : Fseq_space_d (kp_pair_l (ZF.modelsKP (lr_model_zf_l hZF))) w w T)
    (least : Jp_min_d (kp_pair_l (ZF.modelsKP (lr_model_zf_l hZF))) φ w S b T a c)
    (present : Jp_d (kp_pair_l (ZF.modelsKP (lr_model_zf_l hZF))) φ S b a c A)
    (query : Lq_signed_d hZF φ p w.val a.val x.val) : Jp_sign_d p x A := by
  obtain ⟨v,d,a',x',S',T',c',D,ev,ea,ex,_,seed',finite',present',least',_,sign⟩ := query.native_l hZF hc
  have eω : v = w := Subtype.ext ev
  have ea' : a' = a := Subtype.ext ea
  have ex' : x' = x := Subtype.ext ex
  subst v a' x'
  have eb := baire_unique_l (kp_pair_l (ZF.modelsKP (lr_model_zf_l hZF))) (lr_model_zf_l hZF).1 seed'.1 seed.1
  subst d
  exact (least'.same_payoff_l (lr_model_zf_l hZF) seed'.2 seed.2 finite' finite least present' present).2 ▸ sign

/-- 正负上传断言互斥；两个见证的最小坏收益由相同实数参数唯一识别。 -/
theorem Lq_signed_d.disjoint_l {φ : Formula 1 4} (hc : φ.FreeClosed) {ω a x : M.Domain}
    (yes : Lq_signed_d hZF φ true ω a x) : ¬ Lq_signed_d hZF φ false ω a x := by
  intro no
  obtain ⟨w,b,a',x',S,T,c,A,ew,ea,ex,_,seed,finite,present,least,_,sign⟩ := yes.native_l hZF hc
  have no' : Lq_signed_d hZF φ false w.val a'.val x'.val := by simpa only [ew,ea,ex] using no
  exact (no'.sign_l hZF hc seed finite least present) sign

end YesMetaZFC.SetTheory.InnerModel.Relative
