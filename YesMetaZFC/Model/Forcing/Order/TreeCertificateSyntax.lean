import YesMetaZFC.Model.Forcing.Order.NameLetters
import YesMetaZFC.Model.Forcing.Order.JointParameters
import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.Model.Forcing.Order.NameContext
import YesMetaZFC.Model.Forcing.Order.QueryTree
import YesMetaZFC.Model.SetTheory.Reflection.SkolemWitnessTree

/-! # 实际树字母、投影图和登记列的有限公式

逐项编码已有证书的全部字段；满足公式当且仅当原证书成立。
这些公式用于同时反射原树的坐标空间，不能以节点谓词代替投影和登记证书。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}}

def cl_pair_read_m {n} (Y d h : Term n) : Formula 1 n := set[n] ⟪∀ v x y,
  v ∈ ⌜Y⌝ₛ → ⌜kpair_m⌝ₚ(v,x,y) → ⌜rd_entry0_m⌝ₚ(v,x,⌜d⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(v,y,⌜h⌝ₛ)⟫
derive_free_closed cl_pair_read_m

theorem cl_pair_read_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Y d h : Term n) :
    Formula.satisfies ρ (cl_pair_read_m Y d h) ↔
      ∀ v x y, M.mem v (Y.eval ρ) → KPair_d M v x y →
        Rd_entry_d v x (d.eval ρ) ∧ Rd_entry_d v y (h.eval ρ) := by
  simp only [cl_pair_read_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_conj_iff,kpair_sat_l M hE,rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def jt_letters_m {n} (ω A B Z W Y a b c d l r : Term n) : Formula 1 n := set[n] ⟪
  ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜Z⌝ₛ,⌜A⌝ₛ,⌜B⌝ₛ) ∧
  ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜W⌝ₛ,⌜ω⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜Y⌝ₛ,⌜Z⌝ₛ,⌜W⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜a⌝ₛ,⌜Y⌝ₛ,⌜Z⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜b⌝ₛ,⌜Y⌝ₛ,⌜W⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜c⌝ₛ,⌜Z⌝ₛ,⌜A⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜d⌝ₛ,⌜Z⌝ₛ,⌜B⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜l⌝ₛ,⌜W⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜r⌝ₛ,⌜W⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜cl_pair_read_m⌝ₚ(⌜Z⌝ₛ,⌜c⌝ₛ,⌜d⌝ₛ) ∧
  ⌜cl_pair_read_m⌝ₚ(⌜W⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ) ∧
  ⌜cl_pair_read_m⌝ₚ(⌜Y⌝ₛ,⌜a⌝ₛ,⌜b⌝ₛ)⟫
derive_free_closed jt_letters_m

theorem jt_letters_sat_l {n} (ρ : Env M n) (ω A B Z W Y a b c d l r : Term n) :
    Formula.satisfies ρ (jt_letters_m ω A B Z W Y a b c d l r) ↔
      Jt_letters_d hZF (ω.eval ρ) (A.eval ρ) (B.eval ρ) (Z.eval ρ) (W.eval ρ) (Y.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) (d.eval ρ) (l.eval ρ) (r.eval ρ) := by
  simp only [jt_letters_m,Formula.satisfies_conj_iff,Formula.satisfies_isCartesianProduct_iff I,Formula.satisfies_isFunctionFromTo_iff I hZF.1,cl_pair_read_sat_l hZF.1]
  constructor <;> rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ <;> exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩

def nr_letters_m {n} (ω A Z W H a b c d l r Y dx dh : Term n) : Formula 1 n := set[n] ⟪
  ⌜jt_letters_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜ω⌝ₛ,⌜Z⌝ₛ,⌜W⌝ₛ,⌜H⌝ₛ,⌜a⌝ₛ,⌜b⌝ₛ,⌜c⌝ₛ,⌜d⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ) ∧
  ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜Y⌝ₛ,⌜ω⌝ₛ,⌜H⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜dx⌝ₛ,⌜Y⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜dh⌝ₛ,⌜Y⌝ₛ,⌜H⌝ₛ) ∧
  ⌜cl_pair_read_m⌝ₚ(⌜Y⌝ₛ,⌜dx⌝ₛ,⌜dh⌝ₛ)⟫
derive_free_closed nr_letters_m

theorem nr_letters_sat_l {n} (ρ : Env M n) (ω A Z W H a b c d l r Y dx dh : Term n) :
    Formula.satisfies ρ (nr_letters_m ω A Z W H a b c d l r Y dx dh) ↔
      Nr_letters_d hZF (ω.eval ρ) (A.eval ρ) (Z.eval ρ) (W.eval ρ) (H.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) (d.eval ρ) (l.eval ρ) (r.eval ρ) (Y.eval ρ) (dx.eval ρ) (dh.eval ρ) := by
  simp only [nr_letters_m,Formula.satisfies_conj_iff,jt_letters_sat_l hZF,Formula.satisfies_isCartesianProduct_iff I,Formula.satisfies_isFunctionFromTo_iff I hZF.1,cl_pair_read_sat_l hZF.1]
  constructor <;> rintro ⟨h0,h1,h2,h3,h4⟩ <;> exact ⟨h0,h1,h2,h3,h4⟩

def jt_projection_m {n} (a c d ds hg lg de df : Term n) : Formula 1 n := set[n] ⟪∃ s p g,
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ,⌜a⌝ₛ,s) ∧
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ds⌝ₛ,s,⌜de⌝ₛ) ∧
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜d⌝ₛ,⌜a⌝ₛ,p) ∧
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜hg⌝ₛ,p,g) ∧
  ⌜fseq_recode_m (𝒞 := kpair_convention_l)⌝ₚ(⌜lg⌝ₛ,g,⌜df⌝ₛ)⟫
derive_free_closed jt_projection_m

theorem jt_projection_sat_l {n} (ρ : Env M n) (a c d ds hg lg de df : Term n) :
    Formula.satisfies ρ (jt_projection_m a c d ds hg lg de df) ↔
      Jt_projection_d hZF (a.eval ρ) (c.eval ρ) (d.eval ρ) (ds.eval ρ) (hg.eval ρ) (lg.eval ρ) (de.eval ρ) (df.eval ρ) := by
  simp only [jt_projection_m,Jt_projection_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fseq_recode_sat_l I,Definitional.Term.eval_weaken]
  rfl

def jt_params_m {n} (ω X Q T C : Term n) : Formula 1 n := set[n] ⟪
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜C⌝ₛ) ∧ (∃ i, ⌜rd_entry0_m⌝ₚ(i,⌜Q⌝ₛ,⌜C⌝ₛ)) ∧
    (∃ i, ⌜rd_entry0_m⌝ₚ(i,⌜T⌝ₛ,⌜C⌝ₛ))⟫
derive_free_closed jt_params_m

theorem jt_params_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω X Q T C : Term n) :
    Formula.satisfies ρ (jt_params_m ω X Q T C) ↔ Jt_params_d (ω.eval ρ) (X.eval ρ) (Q.eval ρ) (T.eval ρ) (C.eval ρ) := by
  simp only [jt_params_m,Formula.satisfies_conj_iff,Formula.satisfies_exists_iff,fn0_sat_l hE,
    rd_entry0_sat_l hE,Definitional.Term.eval_weaken]
  constructor <;> rintro ⟨f,q,t⟩ <;> exact ⟨f,q,t⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 构枝所用整套有限树证书的原公式

每个公式保存全部字母空间、实际投影、有限列空间、树闭性和精确节点方程。
语义等价直接恢复已有证书，所以反射后的构枝使用原树的全部数据。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def sh_tree_m {n} (ω c X R u C L T E K Q D J Y d h F A : Term n) : Formula 1 n := set[n] ⟪
  ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ,⌜X⌝ₛ,⌜R⌝ₛ) ∧
  ⌜ssk_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜c⌝ₛ,⌜X⌝ₛ,⌜u⌝ₛ,⌜C⌝ₛ,⌜L⌝ₛ,⌜T⌝ₛ,⌜E⌝ₛ,⌜K⌝ₛ) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,⌜Q⌝ₛ) ∧
  ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜D⌝ₛ,⌜T⌝ₛ,⌜Q⌝ₛ) ∧
  ⌜Formula.isInjectionFromTo kpair_convention_l⌝ₚ(⌜J⌝ₛ,⌜D⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜Y⌝ₛ,⌜X⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜d⌝ₛ,⌜Y⌝ₛ,⌜X⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜h⌝ₛ,⌜Y⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜cl_pair_read_m⌝ₚ(⌜Y⌝ₛ,⌜d⌝ₛ,⌜h⌝ₛ) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜Y⌝ₛ,⌜F⌝ₛ) ∧
  ⌜tree_m⌝ₚ(⌜F⌝ₛ,⌜A⌝ₛ) ∧
  (∀ p, p ∈ ⌜A⌝ₛ ↔ ⌜cl_word_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜T⌝ₛ,⌜J⌝ₛ,⌜K⌝ₛ,⌜Y⌝ₛ,⌜d⌝ₛ,⌜h⌝ₛ,p))⟫
derive_free_closed sh_tree_m

theorem sh_tree_sat_l {n} (ρ : Env M n) (ω c X R u C L T E K Q D J Y d h F A : Term n) :
    Formula.satisfies ρ (sh_tree_m ω c X R u C L T E K Q D J Y d h F A) ↔
      Sh_tree_d hZF (ω.eval ρ) (c.eval ρ) (X.eval ρ) (R.eval ρ) (u.eval ρ) (C.eval ρ) (L.eval ρ) (T.eval ρ) (E.eval ρ) (K.eval ρ) (Q.eval ρ) (D.eval ρ) (J.eval ρ) (Y.eval ρ) (d.eval ρ) (h.eval ρ) (F.eval ρ) (A.eval ρ) := by
  simp only [sh_tree_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,smdl_sat_l I,ssk_sat_l I hZF.1,fseq_space_sat_l I hZF.1,Formula.satisfies_isCartesianProduct_iff I,
    Formula.satisfies_isInjectionFromTo_iff I hZF.1,Formula.satisfies_isFunctionFromTo_iff I hZF.1,
    cl_pair_read_sat_l hZF.1,tree_sat_l,cl_word_sat_l hZF,Definitional.Term.eval_weaken]
  constructor <;> rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ <;> exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩

def gn_tree_m {n} (ω X Q T Z Y d h l r F A : Term n) : Formula 1 n := set[n] ⟪
  ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜Z⌝ₛ,⌜Q⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜Y⌝ₛ,⌜X⌝ₛ,⌜Z⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜d⌝ₛ,⌜Y⌝ₛ,⌜X⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜h⌝ₛ,⌜Y⌝ₛ,⌜Z⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜l⌝ₛ,⌜Z⌝ₛ,⌜Q⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜r⌝ₛ,⌜Z⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜cl_pair_read_m⌝ₚ(⌜Z⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ) ∧
  ⌜cl_pair_read_m⌝ₚ(⌜Y⌝ₛ,⌜d⌝ₛ,⌜h⌝ₛ) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜Y⌝ₛ,⌜F⌝ₛ) ∧
  ⌜tree_m⌝ₚ(⌜F⌝ₛ,⌜A⌝ₛ) ∧
  (∀ p, p ∈ ⌜A⌝ₛ ↔ ⌜gn_word_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,⌜Y⌝ₛ,⌜d⌝ₛ,⌜h⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ,p))⟫
derive_free_closed gn_tree_m

theorem gn_tree_sat_l {n} (ρ : Env M n) (ω X Q T Z Y d h l r F A : Term n) :
    Formula.satisfies ρ (gn_tree_m ω X Q T Z Y d h l r F A) ↔
      Gn_tree_d hZF (ω.eval ρ) (X.eval ρ) (Q.eval ρ) (T.eval ρ) (Z.eval ρ) (Y.eval ρ) (d.eval ρ) (h.eval ρ) (l.eval ρ) (r.eval ρ) (F.eval ρ) (A.eval ρ) := by
  simp only [gn_tree_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,fseq_space_sat_l I hZF.1,Formula.satisfies_isCartesianProduct_iff I,
    Formula.satisfies_isFunctionFromTo_iff I hZF.1,cl_pair_read_sat_l hZF.1,tree_sat_l,gn_word_sat_l hZF,Definitional.Term.eval_weaken]
  constructor <;> rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ <;> exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩

def jt_tree_m {n} (ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A : Term n) : Formula 1 n := set[n] ⟪
  ⌜jt_letters_m⌝ₚ(⌜ω⌝ₛ,⌜Ys⌝ₛ,⌜Yg⌝ₛ,⌜Z⌝ₛ,⌜W⌝ₛ,⌜Y⌝ₛ,⌜a⌝ₛ,⌜b⌝ₛ,⌜c⌝ₛ,⌜d⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜ds⌝ₛ,⌜Ys⌝ₛ,⌜X⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜dg⌝ₛ,⌜Yg⌝ₛ,⌜X⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜hg⌝ₛ,⌜Yg⌝ₛ,⌜Zg⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜lg⌝ₛ,⌜Zg⌝ₛ,⌜Q⌝ₛ) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜Ys⌝ₛ,⌜Fs⌝ₛ) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜Yg⌝ₛ,⌜Fg⌝ₛ) ∧
  ⌜tree_m⌝ₚ(⌜Fs⌝ₛ,⌜As⌝ₛ) ∧
  ⌜tree_m⌝ₚ(⌜Fg⌝ₛ,⌜Ag⌝ₛ) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜Y⌝ₛ,⌜F⌝ₛ) ∧
  ⌜tree_m⌝ₚ(⌜F⌝ₛ,⌜A⌝ₛ) ∧
  (∀ p, p ∈ ⌜A⌝ₛ ↔ ⌜jt_word_m⌝ₚ(⌜ω⌝ₛ,⌜Y⌝ₛ,⌜As⌝ₛ,⌜Ag⌝ₛ,⌜ds⌝ₛ,⌜dg⌝ₛ,⌜hg⌝ₛ,⌜lg⌝ₛ,⌜a⌝ₛ,⌜b⌝ₛ,⌜c⌝ₛ,⌜d⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ,⌜C⌝ₛ,p))⟫
derive_free_closed jt_tree_m

theorem jt_tree_sat_l {n} (ρ : Env M n) (ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A : Term n) :
    Formula.satisfies ρ (jt_tree_m ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A) ↔
      Jt_tree_d hZF (ω.eval ρ) (X.eval ρ) (Q.eval ρ) (C.eval ρ) (Ys.eval ρ) (Yg.eval ρ) (Zg.eval ρ) (Fs.eval ρ) (As.eval ρ) (Fg.eval ρ) (Ag.eval ρ) (ds.eval ρ) (dg.eval ρ) (hg.eval ρ) (lg.eval ρ) (Z.eval ρ) (W.eval ρ) (Y.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) (d.eval ρ) (l.eval ρ) (r.eval ρ) (F.eval ρ) (A.eval ρ) := by
  simp only [jt_tree_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,jt_letters_sat_l hZF,Formula.satisfies_isFunctionFromTo_iff I hZF.1,
    fseq_space_sat_l I hZF.1,tree_sat_l,jt_word_sat_l hZF,Definitional.Term.eval_weaken]
  constructor <;> rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ <;> exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩

def nr_tree_m {n} (ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S : Term n) : Formula 1 n := set[n] ⟪
  ⌜nr_letters_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜Z⌝ₛ,⌜W⌝ₛ,⌜H⌝ₛ,⌜a⌝ₛ,⌜b⌝ₛ,⌜c⌝ₛ,⌜d⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ,⌜Y⌝ₛ,⌜dx⌝ₛ,⌜dh⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜de⌝ₛ,⌜A⌝ₛ,⌜X⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜df⌝ₛ,⌜A⌝ₛ,⌜Q⌝ₛ) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜F₀⌝ₛ) ∧
  ⌜tree_m⌝ₚ(⌜F₀⌝ₛ,⌜A₀⌝ₛ) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜Y⌝ₛ,⌜F⌝ₛ) ∧
  ⌜tree_m⌝ₚ(⌜F⌝ₛ,⌜S⌝ₛ) ∧
  (∀ p, p ∈ ⌜S⌝ₛ ↔ ⌜nr_word_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,⌜Y⌝ₛ,⌜A₀⌝ₛ,⌜de⌝ₛ,⌜df⌝ₛ,⌜a⌝ₛ,⌜b⌝ₛ,⌜c⌝ₛ,⌜d⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ,⌜dx⌝ₛ,⌜dh⌝ₛ,p))⟫
derive_free_closed nr_tree_m

theorem nr_tree_sat_l {n} (ρ : Env M n) (ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S : Term n) :
    Formula.satisfies ρ (nr_tree_m ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S) ↔
      Nr_tree_d hZF (ω.eval ρ) (X.eval ρ) (Q.eval ρ) (T.eval ρ) (A.eval ρ) (F₀.eval ρ) (A₀.eval ρ) (de.eval ρ) (df.eval ρ) (Z.eval ρ) (W.eval ρ) (H.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) (d.eval ρ) (l.eval ρ) (r.eval ρ) (Y.eval ρ) (dx.eval ρ) (dh.eval ρ) (F.eval ρ) (S.eval ρ) := by
  simp only [nr_tree_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,nr_letters_sat_l hZF,Formula.satisfies_isFunctionFromTo_iff I hZF.1,
    fseq_space_sat_l I hZF.1,tree_sat_l,nr_word_sat_l hZF,Definitional.Term.eval_weaken]
  constructor <;> rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ <;> exact ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩

def qs_tree_m {n} (φ : Formula 1 4) (sign : Bool) (X Q T σ ω a₀ Y de df a b c d l r dx dh F S S' : Term n) : Formula 1 n := set[n] ⟪
  ⌜tree_m⌝ₚ(⌜F⌝ₛ,⌜S'⌝ₛ) ∧ (∀ q, q ∈ ⌜S'⌝ₛ ↔ q ∈ ⌜S⌝ₛ ∧
    ⌜qs_word_m φ sign⌝ₚ(⌜X⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,⌜σ⌝ₛ,⌜ω⌝ₛ,⌜a₀⌝ₛ,⌜Y⌝ₛ,⌜de⌝ₛ,⌜df⌝ₛ,⌜a⌝ₛ,⌜b⌝ₛ,⌜c⌝ₛ,⌜d⌝ₛ,⌜l⌝ₛ,⌜r⌝ₛ,⌜dx⌝ₛ,⌜dh⌝ₛ,q))⟫

@[simp] theorem qs_tree_closed_l {n} {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool)
    (X Q T σ ω a₀ Y de df a b c d l r dx dh F S S' : Term n)
    (h0 : X.freeSupport = []) (h1 : Q.freeSupport = []) (h2 : T.freeSupport = []) (h3 : σ.freeSupport = []) (h4 : ω.freeSupport = []) (h5 : a₀.freeSupport = []) (h6 : Y.freeSupport = []) (h7 : de.freeSupport = []) (h8 : df.freeSupport = []) (h9 : a.freeSupport = []) (h10 : b.freeSupport = []) (h11 : c.freeSupport = []) (h12 : d.freeSupport = []) (h13 : l.freeSupport = []) (h14 : r.freeSupport = []) (h15 : dx.freeSupport = []) (h16 : dh.freeSupport = []) (h17 : F.freeSupport = []) (h18 : S.freeSupport = []) (h19 : S'.freeSupport = []) :
    (qs_tree_m φ sign X Q T σ ω a₀ Y de df a b c d l r dx dh F S S').FreeClosed := by
  simp -implicitDefEqProofs [qs_tree_m,Definitional.Formula.FreeClosed,hc,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem qs_tree_sat_l {n} {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool)
    (ρ : Env M n) (X Q T σ ω a₀ Y de df a b c d l r dx dh F S S' : Term n)
    {A F₀ A₀ Z W H : M.Domain}
    (base : Nr_tree_d hZF (ω.eval ρ) (X.eval ρ) (Q.eval ρ) (T.eval ρ) A F₀ A₀
      (de.eval ρ) (df.eval ρ) Z W H (a.eval ρ) (b.eval ρ) (c.eval ρ) (d.eval ρ) (l.eval ρ) (r.eval ρ) (Y.eval ρ) (dx.eval ρ) (dh.eval ρ) (F.eval ρ) (S.eval ρ)) :
    Formula.satisfies ρ (qs_tree_m φ sign X Q T σ ω a₀ Y de df a b c d l r dx dh F S S') ↔ Qs_tree_d hZF φ sign base (σ.eval ρ) (a₀.eval ρ) (S'.eval ρ) := by
  simp only [qs_tree_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,tree_sat_l,qs_word_sat_l hZF hc,Definitional.Term.eval_weaken]
  constructor <;> rintro ⟨tree,nodes⟩ <;> exact ⟨tree,nodes⟩

end YesMetaZFC.Model.Forcing.Internal
