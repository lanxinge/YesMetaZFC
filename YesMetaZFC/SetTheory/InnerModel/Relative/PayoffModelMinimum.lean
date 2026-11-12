import YesMetaZFC.SetTheory.InnerModel.Relative.TruthSyntax
import YesMetaZFC.SetTheory.InnerModel.HOD.Models
import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffLayer
import YesMetaZFC.SetTheory.Ord.Code.Natural
import YesMetaZFC.SetTheory.InnerModel.OD.BinaryParameters
import YesMetaZFC.Model.SetTheory.Truth.SetTruthReals
import YesMetaZFC.SetTheory.Ord.Code.SquareCertificate
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift
import YesMetaZFC.SetTheory.Ord.DefinableMinimum

/-! # 派生 Jensen 模型的实际有限参数表示

先在已有的 HOD(A) 模型中重算同一个种子和序数处的 Jensen 层，
Σ₁ 递归证书的向外保持及唯一性识别背景原层。对序数上函数组成的
实数族 B，B 及其传递种子都属于 HOD(B)，故派生层元素亦然。
最后由已有 OD 解码得到一个序数码及一条内部有限 B 参数列；
不把内部有限列假定为宿主有限列表，也不假定 B 已包含所有实数。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem ja_hereditary_l {k : Bool} {A S α Y : M.Domain}
    (seed : Ha_d k A S) (layer : Ja_d S α Y) : Ha_d k A Y := by
  let N := ha_model_l hZF k A
  let s : N.Domain := ⟨S,seed⟩
  let a : N.Domain := ⟨α,ha_ordinal_l hZF k A layer.1⟩
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full (x : N.Domain) y : M.mem y x.val ↔ ∃ z : N.Domain, N.mem z x ∧ z.val = y :=
    ⟨fun h => ⟨⟨y,ha_trans_l x.property h⟩,h,rfl⟩,fun ⟨_,h,eq⟩ => eq ▸ h⟩
  have native : N.Models KPi := ZF.models_kpi_l (ha_model_zf_l hZF k A)
  obtain ⟨U,hu⟩ := ja_value_exists_l (M := N) s native a
  have image := ja_value_image_l (M := N) (N := M) Subtype.val inj full hu
  have eq : U.val = Y := ja_value_unique_l S (ZF.models_kpi_l hZF) image layer.2
  exact eq ▸ U.property

/-- 基集属于实际遗传参数模型时，整个相对 Jensen 并类包含于该模型。 -/
theorem la_hereditary_l {k : Bool} {A S x : M.Domain}
    (seed : Ha_d k A S) (hx : La_d S x) : Ha_d k A x := by
  obtain ⟨α,Y,layer,member⟩ := hx
  exact ha_trans_l (ja_hereditary_l hZF seed layer) member

theorem hp_function_family_l {ω B : M.Domain} (ordinal : M.IsOrdinal ω)
    (functions : ∀ x, M.mem x B → Fn0_d ω ω x) : Hp_d B B := by
  apply ha_of_members_l hZF (oa_parameter_l hZF true B)
  intro x hx
  apply ha_of_members_l hZF (op_member_l hZF hx)
  intro p hp
  obtain ⟨i,hi,j,hj,pair⟩ := (functions x hx).1 p hp
  exact ha_kpair_l hZF (ha_ordinal_l hZF true B (ordinal.mem hi))
    (ha_ordinal_l hZF true B (ordinal.mem hj)) pair

/-- 任意函数实数族产生的相对层元素，由整个实数族、内部有限实数列及
一个序数码唯一定义；不要求该族已是背景的完整 Baire 空间。 -/
theorem dr_parameters_l {ω B S x : M.Domain} (hw : M.IsOmega ω)
    (functions : ∀ y, M.mem y B → Fn0_d ω ω y) (tc : Tc_d B S) (hx : La_d S x) :
    ∃ n s p q, M.mem n ω ∧ Fn0_d n B s ∧ KPair_d M p B s ∧
      M.IsOrdinal q ∧ Ob_eval_d I q p x := by
  have base := hp_function_family_l hZF (hw.isOrdinal (ZF.modelsKP hZF)) functions
  have defined := ha_oa_l (la_hereditary_l hZF (ha_tc_closed_l hZF base tc) hx)
  obtain ⟨n,s,p,hn,seq,pair,code⟩ := (op_statement_l hZF hw).mp defined
  obtain ⟨q,value⟩ := (ob_code_l I hZF).mp code
  exact ⟨n,s,p,q,hn,fn0_of_function_l (ZF.modelsKP hZF) seq,pair,
    value.elim (fun _ h => od_eval_ordinal_l I hZF h.1),value⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 内部有限实数列合并为一个二值实数参数

使用规范序数配对编码行列坐标，未使用的坐标填零。解码只依赖原实数族、
列长度及这一个实数，不引入另选的自然数配对函数作为参数。
长度允许内部非标准；实际函数图由分离、替代直接构造。最后再作规范
二值编码，唯一解码保证保留原定义能力，并使指定参数落入坍塌固定类。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Fr_read_d (J : kpair_convention_l.Interpretation M) (ω B n r s : M.Domain) : Prop := Fn0_d n B s ∧
  ∀ i x, M.PairMember J i x s → ∀ j v, M.PairMember J j v x ↔
    M.mem j ω ∧ ∃ k, Oc_pair_d J i j k ∧ M.PairMember J k v r

def fr_read_m {d} (ω B n r s : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜n⌝ₛ,⌜B⌝ₛ,⌜s⌝ₛ) ∧ (∀ i, ∀ x,
    ⌜(Formula.orderedPairMem kpair_convention_l)⌝ₚ(i,x,⌜s⌝ₛ) → ∀ j, ∀ v,
      (⌜(Formula.orderedPairMem kpair_convention_l)⌝ₚ(j,v,x) ↔ j ∈ ⌜ω⌝ₛ ∧
        (∃ k, ⌜(oc_pair_m (𝒞 := kpair_convention_l))⌝ₚ(i,j,k) ∧
          ⌜(Formula.orderedPairMem kpair_convention_l)⌝ₚ(k,v,⌜r⌝ₛ))))⟫
derive_free_closed fr_read_m

theorem fr_read_sat_l (J : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω B n r s : Term d) :
    Formula.satisfies ρ (fr_read_m ω B n r s) ↔
      Fr_read_d J (ω.eval ρ) (B.eval ρ) (n.eval ρ) (r.eval ρ) (s.eval ρ) := by
  simp only [fr_read_m,Fr_read_d,Formula.satisfies_conj_iff,fn0_sat_l hE,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,Formula.satisfies_orderedPairMem_iff J,
    oc_pair_sat_l J hE,Definitional.Term.eval_weaken]
  rfl

theorem fr_read_unique_l (hKP : M.Models KP) {ω B n r s t : M.Domain}
    (functions : ∀ x, M.mem x B → Fn0_d ω ω x)
    (left : Fr_read_d (kp_pair_l hKP) ω B n r s) (right : Fr_read_d (kp_pair_l hKP) ω B n r t) : s = t := by
  have fs := fn0_function_l hKP left.1
  have ft := fn0_function_l hKP right.1
  have sub {s t} (a : Fr_read_d (kp_pair_l hKP) ω B n r s) (b : Fr_read_d (kp_pair_l hKP) ω B n r t)
      i x (ix : M.PairMember (kp_pair_l hKP) i x s) : M.PairMember (kp_pair_l hKP) i x t := by
    obtain ⟨y,hy,iy⟩ := b.1.2.1 i (a.1.bound_l ix).1
    have fx := fn0_function_l hKP (functions x (a.1.bound_l ix).2)
    have fy := fn0_function_l hKP (functions y hy)
    have eq : x = y := fx.1.1.eq_of_pairMember_iff hKP.1 fy.1.1
      (fun j v => (a.2 i x ix j v).trans (b.2 i y iy j v).symm)
    exact eq.symm ▸ iy
  exact fs.1.1.eq_of_pairMember_iff hKP.1 ft.1.1 (fun i x => ⟨sub left right i x,sub right left i x⟩)

include hZF

theorem fr_encode_l {ω B n s : M.Domain} (hw : M.IsOmega ω) (hn : M.mem n ω)
    (functions : ∀ x, M.mem x B → Fn0_d ω ω x) (seq : Fn0_d n B s) :
    ∃ r, Fn0_d ω ω r ∧ Fr_read_d I ω B n r s := by
  have fs := fn0_function_l (ZF.modelsKP hZF) seq
  obtain ⟨z,_,hz⟩ := hw.1.1
  let active k := ∃ i, M.mem i n ∧ ∃ j, M.mem j ω ∧ Oc_pair_d I i j k
  let ρ : Env M 4 := ⟨fun i => [ω,n,s,z].get i,fun _ => z⟩
  let φ : BinarySchema 4 := { body := set[6] ⟪
    (∃ i ∈ ⌜(.bound 3 : Term 6)⌝ₛ, ∃ j ∈ ⌜(.bound 2 : Term 6)⌝ₛ, ∃ x,
      ⌜(Formula.orderedPairMem kpair_convention_l)⌝ₚ(i,x,⌜(.bound 4 : Term 6)⌝ₛ) ∧
      ⌜(oc_pair_m (𝒞 := kpair_convention_l))⌝ₚ(i,j,⌜(.bound 1 : Term 6)⌝ₛ) ∧
      ⌜(Formula.orderedPairMem kpair_convention_l)⌝ₚ(j,⌜(.newest : Term 6)⌝ₛ,x)) ∨
    ((¬ (∃ i ∈ ⌜(.bound 3 : Term 6)⌝ₛ, ∃ j ∈ ⌜(.bound 2 : Term 6)⌝ₛ,
      ⌜(oc_pair_m (𝒞 := kpair_convention_l))⌝ₚ(i,j,⌜(.bound 1 : Term 6)⌝ₛ))) ∧
        ⌜(.newest : Term 6)⌝ₛ = ⌜(.bound 5 : Term 6)⌝ₛ)⟫ }
  have sat k v : φ.denote ρ k v ↔
      (∃ i, M.mem i n ∧ ∃ j, M.mem j ω ∧ ∃ x,
        M.PairMember I i x s ∧ Oc_pair_d I i j k ∧ M.PairMember I j v x) ∨
      (¬ active k ∧ v = z) := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_disj_iff,Formula.satisfies_existsMem_iff,
      Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_orderedPairMem_iff I,
      oc_pair_sat_l I hZF.1,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Definitional.Term.eval_weaken]
    rfl
  have total k : ∃ v, φ.denote ρ k v := by
    classical
    by_cases h : active k
    · obtain ⟨i,hi,j,hj,code⟩ := h
      obtain ⟨x,hx,ix⟩ := seq.2.1 i hi
      obtain ⟨v,_,jv⟩ := (functions x hx).2.1 j hj
      exact ⟨v,(sat k v).mpr (Or.inl ⟨i,hi,j,hj,x,ix,code,jv⟩)⟩
    · exact ⟨z,(sat k z).mpr (Or.inr ⟨h,rfl⟩)⟩
  have unique k v w (hv : φ.denote ρ k v) (hw : φ.denote ρ k w) : v = w := by
    rcases (sat k v).mp hv with ⟨i,hi,j,hj,x,ix,code,jv⟩ | ⟨no,rfl⟩ <;>
      rcases (sat k w).mp hw with ⟨a,ha,b,hb,y,ay,code',bw⟩ | ⟨no',rfl⟩
    · obtain ⟨ei,ej⟩ := oc_pair_injective_l I hZF code code'
      subst a b
      have eq := fs.1.2 i x y ix ay
      subst y
      exact (fn0_function_l (ZF.modelsKP hZF) (functions x (seq.bound_l ix).2)).1.2 j v w jv bw
    · exact (no' ⟨i,hi,j,hj,code⟩).elim
    · exact (no ⟨a,ha,b,hb,code'⟩).elim
    · rfl
  have bounded k v (hv : φ.denote ρ k v) : M.mem v ω := by
    rcases (sat k v).mp hv with ⟨_,_,j,_,x,ix,_,jv⟩ | ⟨_,rfl⟩
    · exact ((functions x (seq.bound_l ix).2).bound_l jv).2
    · exact hz
  obtain ⟨r,fr,edges⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω)
    (fun k _ => total k) (fun k _ => unique k) (fun k v _ => bounded k v)
  refine ⟨r,fn0_of_function_l (ZF.modelsKP hZF) fr,seq,fun i x ix j v => ?_⟩
  have hi := (seq.bound_l ix).1
  have fx := functions x (seq.bound_l ix).2
  constructor
  · intro jv
    have hj := (fx.bound_l jv).1
    have hiω := hw.transitive (ZF.modelsKP hZF) n hn i hi
    obtain ⟨k,code⟩ := oc_pair_exists_l I hZF (hw.members_areOrdinals (ZF.modelsKP hZF) i hiω)
      (hw.members_areOrdinals (ZF.modelsKP hZF) j hj)
    exact ⟨hj,k,code,(edges k v).mpr ⟨oc_pair_natural_l I hZF hw hiω hj code,
      (sat k v).mpr (Or.inl ⟨i,hi,j,hj,x,ix,code,jv⟩)⟩⟩
  · rintro ⟨hj,k,code,kv⟩
    rcases (sat k v).mp ((edges k v).mp kv).2 with ⟨a,ha,b,_,y,ay,code',bv⟩ | ⟨no,_⟩
    · obtain ⟨ei,ej⟩ := oc_pair_injective_l I hZF code' code
      subst a b
      exact fs.1.2 i y x ay ix ▸ bv
    · exact (no ⟨i,hi,j,hj,code⟩).elim

/-- 完整 Baire 基集时，合并后再取二值编码；任意层元素只需
一个二值实数参数和一个序数码，整个基集继续作为固定集合参数。 -/
theorem lr_real_parameter_l {ω B S x : M.Domain} (space : Baire_d I ω B)
    (tc : Tc_d B S) (hx : La_d S x) :
    ∃ a p q, M.mem a B ∧ Bc_binary_d ω a ∧ KPair_d M p B a ∧ M.IsOrdinal q ∧ Ob_eval_d I q p x := by
  have functions y (hy : M.mem y B) := fn0_of_function_l (ZF.modelsKP hZF) ((space.2 y).mp hy)
  obtain ⟨n,s,p,q,hn,seq,pair,_,value⟩ := dr_parameters_l hZF space.1 functions tc hx
  obtain ⟨a,real,read⟩ := fr_encode_l hZF space.1 hn functions seq
  obtain ⟨a₀,binary,decoded⟩ := bc_encode_l hZF space.1 real
  obtain ⟨b,pair'⟩ := (kp_pair_l (ZF.modelsKP hZF)).total B a₀
  obtain ⟨base,bitParam⟩ := ob_pair_components_l hZF b (ob_parameter_l hZF b) pair'
  have param : Ob_d b a := ob_trans_l hZF bitParam (bc_read_ob_l hZF space.1 decoded)
  let φ : UnarySchema 4 := { body := fr_read_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) .newest }
  let ρ : Env M 4 := ⟨fun i => [ω,B,n,a].get i,fun _ => a⟩
  have hs : Ob_d b s := ob_closed_l hZF b φ ρ
    (Fin.cases (ob_ordinal_l hZF b (space.1.isOrdinal (ZF.modelsKP hZF)))
      (Fin.cases base (Fin.cases (ob_ordinal_l hZF b (space.1.members_areOrdinals (ZF.modelsKP hZF) n hn))
        (Fin.cases param (fun i => Fin.elim0 i)))))
    (fun t => (fr_read_sat_l I hZF.1 (ρ.push t) (.bound 1) (.bound 2) (.bound 3) (.bound 4) .newest).trans
      ⟨fun h => fr_read_unique_l (ZF.modelsKP hZF) functions h read,fun eq => eq.symm ▸ read⟩)
  have old : Ob_d p x := (ob_code_l I hZF).mpr ⟨q,value⟩
  obtain ⟨c,code⟩ := (ob_code_l I hZF).mp (ob_trans_l hZF (ob_pair_l hZF b base hs pair) old)
  exact ⟨a₀,b,c,(space.2 a₀).mpr (fn0_function_l (ZF.modelsKP hZF) binary.1),binary,pair',
    code.elim (fun _ h => od_eval_ordinal_l I hZF h.1),code⟩

/-- 实际并类无新实数时，在其中重算同一实数族、种子及整个并类。 -/
theorem la_real_self_l {ω B S : M.Domain} (hw : M.IsOmega ω) (tc : Tc_d B S)
    (reals : ∀ x, La_d S x → (Fn0_d ω ω x ↔ M.mem x B)) :
    let D := la_model_l S (ZF.models_kpi_l hZF)
    let hD := la_model_zf_l S hZF tc.1
    ∃ w b s : D.Domain, w.val = ω ∧ b.val = B ∧ s.val = S ∧
      Lr_seed_d hD w b s ∧ ∀ x : D.Domain, La_d s x := by
  let D := la_model_l S (ZF.models_kpi_l hZF)
  have hD : D.Models ZF := la_model_zf_l S hZF tc.1
  let s : D.Domain := ⟨S,la_seed_l S (ZF.models_kpi_l hZF)⟩
  have full (a : D.Domain) y : M.mem y a.val ↔ ∃ b : D.Domain, D.mem b a ∧ b.val = y :=
    ⟨fun h => ⟨⟨y,la_transitive_l S (ZF.models_kpi_l hZF) tc.1 a.property h⟩,h,rfl⟩,
      fun ⟨_,h,eq⟩ => eq ▸ h⟩
  obtain ⟨w,b,ew,eq,space⟩ := la_reals_l S hZF hw tc reals
  have nativeTc : Tc_d b s := by
    refine ⟨fun a ha y hy => tc.1 a.val ha y.val hy,?_,?_⟩
    · change M.mem b.val S
      exact eq.symm ▸ tc.2.1
    · intro T trans member y hy
      have trans' : M.TransitiveSet T.val := by
        intro u hu v hv
        obtain ⟨u,hu,rfl⟩ := (full T u).mp hu
        obtain ⟨v,hv,rfl⟩ := (full u v).mp hv
        exact trans u hu v hv
      have inside : M.mem B T.val := eq ▸ (show M.mem b.val T.val from member)
      exact tc.2.2 T.val trans' inside y.val hy
  exact ⟨w,b,s,ew,eq,rfl,⟨space,nativeTc⟩,fun x => la0_inner_of_outer_l hZF tc.1 x.property⟩

/-- 在真实 L(ℝ) 自身解释参数定义；定义码及解码图都属于同一内模型。 -/
theorem lr_internal_parameter_l {ω B S : M.Domain} (seed : Lr_seed_d hZF ω B S)
    (x : (la_model_l S (ZF.models_kpi_l hZF)).Domain) :
    let D := la_model_l S (ZF.models_kpi_l hZF)
    let hD := la_model_zf_l S hZF seed.2.1
    ∃ b a p q : D.Domain, b.val = B ∧ D.mem a b ∧ Bc_binary_d ω a.val ∧ KPair_d D p b a ∧
      D.IsOrdinal q ∧ Ob_eval_d (kp_pair_l (ZF.modelsKP hD)) q p x := by
  have hD := la_model_zf_l S hZF seed.2.1
  obtain ⟨w,b,s,ew,eq,_,native,self⟩ := la_real_self_l hZF seed.1.1 seed.2
    (fun x _ => (Iff.intro (fn0_function_l (ZF.modelsKP hZF)) (fn0_of_function_l (ZF.modelsKP hZF))).trans (seed.1.2 x).symm)
  obtain ⟨a,p,q,real,binary,pair,ordinal,code⟩ := lr_real_parameter_l hD native.1 native.2 (self x)
  let ρ : Env (la_model_l S (ZF.models_kpi_l hZF)) 2 := ⟨Fin.cases w (fun _ => a),fun _ => w⟩
  have raw := (bc_binary_sat_l hZF.1 _ _ _).mp
    ((la_model_delta_l S (ZF.models_kpi_l hZF) seed.2.1 (bc_binary_delta_l (.bound 0) (.bound 1)) ρ).mp
      ((bc_binary_sat_l hD.1 ρ (.bound 0) (.bound 1)).mpr binary))
  change Bc_binary_d w.val a.val at raw
  exact ⟨b,a,p,q,eq,real,ew ▸ raw,pair,ordinal,code⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 一个固定公式呈示 L(ℝ) 的全部收益集

在 L(ℝ) 内将收益集写成一个实数参数及一个序数码的唯一定义，
再对同一固定解码公式作有限反射。所得实际 Jensen 层包含全部实数，
其成员结构逐点定义原收益；层号和定义码均为背景序数。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 参数次序为完整实数族、指定实数、序数码、待查询实数。 -/
def lr_payoff_m : Formula 1 4 := set[4] ⟪∃ p, ∃ A,
  ⌜kpair_m⌝ₚ(p,⌜(.bound 0 : Term 4)⌝ₛ,⌜(.bound 1 : Term 4)⌝ₛ) ∧
  ⌜ob_eval_m⌝ₚ(⌜(.bound 2 : Term 4)⌝ₛ,p,A) ∧ ⌜(.bound 3 : Term 4)⌝ₛ ∈ A⟫

theorem lr_payoff_closed_l : lr_payoff_m.FreeClosed := by
  simp only [lr_payoff_m,Definitional.Formula.FreeClosed]
  simp -implicitDefEqProofs

theorem lr_payoff_sat_l {B a p q A y : M.Domain} (pair : KPair_d M p B a)
    (code : Ob_eval_d I q p A) :
    Formula.satisfies (⟨fun i => [B,a,q,y].get i,fun _ => B⟩ : Env M 4) lr_payoff_m ↔ M.mem y A := by
  simp only [lr_payoff_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    kpair_sat_l M hZF.1,ob_eval_sat_l I hZF.1,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨p',A',pair',code',member⟩
    have eq : p' = p := kpair_unique_l M hZF.1 pair' pair
    subst p'
    exact ob_eval_unique_l I hZF code' code ▸ member
  · exact fun h => ⟨p,A,pair,code,h⟩

theorem lr_payoff_presentation_l {ω B S : M.Domain} (seed : Lr_seed_d hZF ω B S)
    (A : (la_model_l S (ZF.models_kpi_l hZF)).Domain) (sub : M.MemberSubset A.val B) :
    ∃ a γ q U, M.mem a B ∧ Bc_binary_d ω a ∧ M.IsOrdinal q ∧ Ja_d S γ U ∧
      M.mem B U ∧ M.mem a U ∧ M.mem q U ∧
      ∀ y, M.mem y A.val ↔ M.mem y B ∧ St_d U lr_payoff_m (fun i => [B,a,q,y].get i) := by
  let D := la_model_l S (ZF.models_kpi_l hZF)
  have hD : D.Models ZF := la_model_zf_l S hZF seed.2.1
  obtain ⟨b,a,p,q,eq,real,binary,pair,ordinal,code⟩ := lr_internal_parameter_l hZF seed A
  obtain ⟨T,cover⟩ := kp_finite_cover_l (ZF.modelsKP hD) [b,a,q]
  obtain ⟨γ,U,layer,tu,closed⟩ := ja_closed_layer_l S hZF seed.2.1
    (lr_queries_l lr_payoff_m lr_payoff_closed_l) T
  have trans := ja_transitive_l S (ZF.models_kpi_l hZF) seed.2.1 layer.2
  have inside v (hv : v ∈ [b,a,q]) : D.mem v U := trans T.val tu v.val (cover v hv).2
  have hb := inside b (by simp)
  have ha := inside a (by simp)
  have hq := inside q (by simp)
  have inj : Function.Injective (Subtype.val : D.Domain → M.Domain) := fun _ _ e => Subtype.ext e
  have full (x : D.Domain) y : M.mem y x.val ↔ ∃ z : D.Domain, D.mem z x ∧ z.val = y :=
    ⟨fun h => ⟨⟨y,la_transitive_l S (ZF.models_kpi_l hZF) seed.2.1 x.property h⟩,h,rfl⟩,
      fun ⟨_,h,e⟩ => e ▸ h⟩
  let δ : Env D 1 := ⟨fun _ => q,fun _ => q⟩
  have oq₀ := (KP.ord0_sat_l (ZF.modelsKP hD) δ (.bound 0)).mpr ordinal
  have oq₁ := (la_model_delta_l S (ZF.models_kpi_l hZF) seed.2.1 (KP.ord0_delta_l (.bound 0)) δ).mp oq₀
  have oq := (KP.ord0_sat_l (ZF.modelsKP hZF)
    (image_env_l (M := D) (N := M) Subtype.val δ) (.bound 0)).mp oq₁
  have haB : M.mem a.val B := eq ▸ (show M.mem a.val b.val from real)
  have hBU : M.mem B U.val := eq ▸ (show M.mem b.val U.val from hb)
  refine ⟨a.val,γ,q.val,U.val,haB,binary,oq,layer,hBU,ha,hq,fun y => ?_⟩
  have point (hy : M.mem y B) : M.mem y A.val ↔
      St_d U.val lr_payoff_m (fun i => [B,a.val,q.val,y].get i) := by
    let y' : D.Domain := ⟨y,la_transitive_l S (ZF.models_kpi_l hZF) seed.2.1 b.property (eq.symm ▸ hy)⟩
    let ρ : Env D 4 := ⟨fun i => [b,a,q,y'].get i,fun _ => b⟩
    have params : ∀ i, D.mem (ρ.bound i) U :=
      Fin.cases hb (Fin.cases ha (Fin.cases hq (Fin.cases (trans B hBU y hy) (fun i => Fin.elim0 i))))
    have reflect := st_reflect_l hD (fun x hx z hz => trans x.val hx z.val hz)
      ⟨b,hb⟩ lr_payoff_m lr_payoff_closed_l closed ρ params
    have out := st_image_l (M := D) (N := M) Subtype.val inj full U lr_payoff_m lr_payoff_closed_l ρ.bound
    have result := (lr_payoff_sat_l hD (y := y') pair code).symm.trans (reflect.trans out)
    have values : (fun i => (ρ.bound i).val) = (fun i => [B,a.val,q.val,y].get i) :=
      funext (Fin.cases eq (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
    rw [values] at result
    exact result
  exact ⟨fun h => ⟨sub y h,(point (sub y h)).mp h⟩,fun h => (point h.1).mpr h.2⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 固定公式及实数参数的实际收益代码

代码为层号与序数参数的规范序数配对。层、满足关系和完整收益成员方程
都在原对象公式中出现；代码唯一决定收益集合。公开呈示入口覆盖 L(ℝ)
的每个收益，不要求调用者提供定义或代码。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def jp_member_m {d} (φ : Formula 1 4) (U B a q y : Term d) : Formula 1 d :=
  st_m φ U (fun i => [B,a,q,y].get i)

theorem jp_member_delta_l {d} (φ : Formula 1 4) (U B a q y : Term d) : (jp_member_m φ U B a q y).IsDelta0 :=
  .conj (.existsMem _ .truth) (.conj
    (.conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) .truth))))
    (st_rel_delta_l ..))

@[simp] theorem jp_member_closed_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (U B a q y : Term d)
    (hU : U.freeSupport = []) (hB : B.freeSupport = []) (ha : a.freeSupport = [])
    (hq : q.freeSupport = []) (hy : y.freeSupport = []) : (jp_member_m φ U B a q y).FreeClosed :=
  st_closed_l φ hc U _ hU (Fin.cases hB (Fin.cases ha (Fin.cases hq (Fin.cases hy (fun i => Fin.elim0 i)))))

theorem jp_member_sat_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (ρ : Env M d) (U B a q y : Term d) :
    Formula.satisfies ρ (jp_member_m φ U B a q y) ↔
      St_d (U.eval ρ) φ (Fin.cases (B.eval ρ) (Fin.cases (a.eval ρ)
        (Fin.cases (q.eval ρ) (Fin.cases (y.eval ρ) Fin.elim0)))) := by
  rw [jp_member_m,st_sat_l φ hc]
  have eq : (fun i : Fin 4 => ([B,a,q,y].get i).eval ρ) =
      Fin.cases (B.eval ρ) (Fin.cases (a.eval ρ) (Fin.cases (q.eval ρ) (Fin.cases (y.eval ρ) Fin.elim0))) :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  exact iff_of_eq (congrArg (St_d (U.eval ρ) φ) eq)

def Jp_d (J : kpair_convention_l.Interpretation M) (φ : Formula 1 4) (S B a c A : M.Domain) : Prop :=
  ∃ γ q U, Oc_pair_d J γ q c ∧ Ja_d S γ U ∧ M.mem B U ∧ M.mem a U ∧ M.mem q U ∧
    ∀ y, M.mem y A ↔ M.mem y B ∧ St_d U φ (Fin.cases B (Fin.cases a (Fin.cases q (Fin.cases y Fin.elim0))))

def jp_m {d} (φ : Formula 1 4) (S B a c A : Term d) : Formula 1 d := set[d] ⟪∃ γ, ∃ q, ∃ U,
  ⌜(oc_pair_m (𝒞 := kpair_convention_l))⌝ₚ(γ,q,⌜c⌝ₛ) ∧
  (⌜KP.ord0_m⌝ₚ(γ) ∧ ⌜ja_value_m⌝ₚ(⌜S⌝ₛ,γ,U)) ∧
  ⌜B⌝ₛ ∈ U ∧ ⌜a⌝ₛ ∈ U ∧ q ∈ U ∧
  (∀ y, y ∈ ⌜A⌝ₛ ↔ y ∈ ⌜B⌝ₛ ∧ ⌜(jp_member_m φ)⌝ₚ(U,⌜B⌝ₛ,⌜a⌝ₛ,q,y))⟫

@[simp] theorem jp_closed_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (S B a c A : Term d)
    (hS : S.freeSupport = []) (hB : B.freeSupport = []) (ha : a.freeSupport = [])
    (hc' : c.freeSupport = []) (hA : A.freeSupport = []) : (jp_m φ S B a c A).FreeClosed := by
  simp -implicitDefEqProofs [jp_m,Definitional.Formula.FreeClosed,hS,hB,ha,hc',hA,hc]

theorem jp_sat_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (ρ : Env M d) (S B a c A : Term d) :
    Formula.satisfies ρ (jp_m φ S B a c A) ↔
      Jp_d I φ (S.eval ρ) (B.eval ρ) (a.eval ρ) (c.eval ρ) (A.eval ρ) := by
  simp -implicitDefEqProofs only [jp_m,Jp_d,Ja_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    oc_pair_sat_l I hZF.1,KP.ord0_sat_l (ZF.modelsKP hZF),ja_value_sat_l,
    Formula.satisfies_mem_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    jp_member_sat_l φ hc,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem Jp_d.ordinal_l {φ S B a c A} (h : Jp_d I φ S B a c A) : M.IsOrdinal c := by
  obtain ⟨_,_,_,code,_⟩ := h
  exact (oc_pair_types_l I hZF code).2.2

theorem Jp_d.unique_l {φ S B a c A D} (left : Jp_d I φ S B a c A) (right : Jp_d I φ S B a c D) : A = D := by
  obtain ⟨γ,q,U,code,layer,_,_,_,members⟩ := left
  obtain ⟨δ,r,V,code',layer',_,_,_,members'⟩ := right
  obtain ⟨eq,eq'⟩ := oc_pair_injective_l I hZF code' code
  subst δ r
  have eq : V = U := ja_value_unique_l S (ZF.models_kpi_l hZF) layer'.2 layer.2
  subst V
  exact hZF.1.eq_of_same_members A D (fun y => (members y).trans (members' y).symm)

theorem jp_presentation_l {ω B S : M.Domain} (seed : Lr_seed_d hZF ω B S)
    (A : (la_model_l S (ZF.models_kpi_l hZF)).Domain) (sub : M.MemberSubset A.val B) :
    ∃ a c, M.mem a B ∧ Descriptive.Bc_binary_d ω a ∧ Jp_d I lr_payoff_m S B a c A.val := by
  obtain ⟨a,γ,q,U,real,binary,ordinal,layer,base,param,index,members⟩ := lr_payoff_presentation_l hZF seed A sub
  obtain ⟨c,code⟩ := oc_pair_exists_l I hZF layer.1 ordinal
  refine ⟨a,c,real,binary,γ,q,U,code,layer,base,param,index,fun y => ?_⟩
  have params : (fun i : Fin 4 => [B,a,q,y].get i) =
      Fin.cases B (Fin.cases a (Fin.cases q (Fin.cases y Fin.elim0))) :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  exact (members y).trans (and_congr_right fun _ => iff_of_eq (congrArg (St_d U lr_payoff_m) params))

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 由原方块图及同一 Jensen 递归图核验收益

层号和序数参数从实际方块读取，层从同一个成员递归证书读取。
原任意公式只在该层的成员结构中求值，故收益成员方程为 Δ₀。
值域内的全局规范收益与该局部检查完全等价，包括全部更早代码。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def ja_cert_m {d} (S D H W : Term d) : Formula 1 d := rc_cert_m ja_op_s (fun _ => S) D H W
derive_free_closed ja_cert_m

theorem ja_cert_delta_l {d} (S D H W : Term d) : (ja_cert_m S D H W).IsDelta0 := rc_cert_delta_l ..

theorem ja_cert_sat_l (hE : Extensional M) {d} (ρ : Env M d) (S D H W : Term d) :
    Formula.satisfies ρ (ja_cert_m S D H W) ↔
      Rc_cert_d ja_op_s (ja_env_l (S.eval ρ)) (D.eval ρ) (H.eval ρ) (W.eval ρ) := by
  rw [ja_cert_m,rc_cert_sat_l hE]
  have move {μ ν : Env M 1} {A F T : M.Domain} (same : μ.bound = ν.bound)
      (h : Rc_cert_d ja_op_s μ A F T) : Rc_cert_d ja_op_s ν A F T := by
    refine ⟨h.trans,h.domain,h.graph,h.hereditary,h.function,fun a ha => ?_⟩
    obtain ⟨R,hr,cut,step⟩ := h.step a ha
    refine ⟨R,hr,cut,fun y hy edge => ?_⟩
    obtain ⟨w,hw,valid⟩ := step y hy edge
    exact ⟨w,hw,(Formula.closed_env_l _ ja_op_s.matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (congrFun same)))))).mp valid⟩
  exact ⟨move rfl,move rfl⟩

def Jp_value_d (φ : Formula 1 4) (B a q Y A : M.Domain) : Prop := M.MemberSubset A B ∧
  ∀ x, M.mem x B → (M.mem x A ↔ St_d Y φ (Fin.cases B (Fin.cases a (Fin.cases q (Fin.cases x Fin.elim0)))))

def jp_value_m {d} (φ : Formula 1 4) (B a q Y A : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.subset⌝ₚ(⌜A⌝ₛ,⌜B⌝ₛ) ∧
  (∀ x ∈ ⌜B⌝ₛ, x ∈ ⌜A⌝ₛ ↔ ⌜(jp_member_m φ)⌝ₚ(⌜Y⌝ₛ,⌜B⌝ₛ,⌜a⌝ₛ,⌜q⌝ₛ,x))⟫

@[simp] theorem jp_value_closed_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (B a q Y A : Term d)
    (hb : B.freeSupport = []) (ha : a.freeSupport = []) (hq : q.freeSupport = [])
    (hy : Y.freeSupport = []) (hA : A.freeSupport = []) : (jp_value_m φ B a q Y A).FreeClosed := by
  simp -implicitDefEqProofs [jp_value_m,Definitional.Formula.FreeClosed,hb,ha,hq,hy,hA,hc]

theorem jp_value_delta_l {d} (φ : Formula 1 4) (B a q Y A : Term d) : (jp_value_m φ B a q Y A).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (jp_member_delta_l ..)))

theorem jp_value_sat_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (ρ : Env M d) (B a q Y A : Term d) :
    Formula.satisfies ρ (jp_value_m φ B a q Y A) ↔ Jp_value_d φ (B.eval ρ) (a.eval ρ) (q.eval ρ) (Y.eval ρ) (A.eval ρ) := by
  simp only [jp_value_m,Jp_value_d,Formula.satisfies_conj_iff,Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,
    jp_member_sat_l φ hc,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem jp_value_exists_l (hKP : M.Models KP) (φ : Formula 1 4) (hc : φ.FreeClosed) (B a q Y : M.Domain) :
    ∃ A, Jp_value_d φ B a q Y A := by
  let ρ : Env M 4 := ⟨fun i => [B,a,q,Y].get i,fun _ => B⟩
  let ψ : Delta0UnarySchema 4 := {
    body := jp_member_m φ (.bound 4) (.bound 1) (.bound 2) (.bound 3) .newest
    freeClosed := jp_member_closed_l φ hc _ _ _ _ _ rfl rfl rfl rfl rfl
    delta0 := jp_member_delta_l .. }
  obtain ⟨A,sep⟩ := KP.separation_exists_d hKP ψ ρ B
  have read x : M.mem x A ↔ M.mem x B ∧ St_d Y φ
      (Fin.cases B (Fin.cases a (Fin.cases q (Fin.cases x Fin.elim0)))) :=
    (sep x).trans (and_congr_right fun _ => jp_member_sat_l φ hc (ρ.push x) _ _ _ _ _)
  exact ⟨A,fun x hx => ((read x).mp hx).1,fun x hx => (read x).trans (and_iff_right hx)⟩

theorem Jp_value_d.unique_l (hE : Extensional M) {φ : Formula 1 4} {B a q Y A D : M.Domain}
    (left : Jp_value_d φ B a q Y A) (right : Jp_value_d φ B a q Y D) : A = D :=
  hE.eq_of_same_members A D (fun x =>
    ⟨fun h => (right.2 x (left.1 x h)).mpr ((left.2 x (left.1 x h)).mp h),
      fun h => (left.2 x (right.1 x h)).mpr ((right.2 x (right.1 x h)).mp h)⟩)

def Jp_local_d (φ : Formula 1 4) (B a c A t X K H W : M.Domain) : Prop :=
  ∃ p, M.mem p X ∧ ∃ γ, M.mem γ t ∧ ∃ q, M.mem q t ∧ ∃ Y, M.mem Y W ∧
    KPair_d M p γ q ∧ Rd_entry_d p c K ∧ Rd_entry_d γ Y H ∧
    M.mem B Y ∧ M.mem a Y ∧ M.mem q Y ∧ Jp_value_d φ B a q Y A

def jp_local_m {d} (φ : Formula 1 4) (B a c A t X K H W : Term d) : Formula 1 d := set[d] ⟪
  ∃ p ∈ ⌜X⌝ₛ, ∃ γ ∈ ⌜t⌝ₛ, ∃ q ∈ ⌜t⌝ₛ, ∃ Y ∈ ⌜W⌝ₛ,
    ⌜kpair0_m⌝ₚ(p,γ,q) ∧ ⌜rd_entry0_m⌝ₚ(p,⌜c⌝ₛ,⌜K⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(γ,Y,⌜H⌝ₛ) ∧
    ⌜B⌝ₛ ∈ Y ∧ ⌜a⌝ₛ ∈ Y ∧ q ∈ Y ∧ ⌜(jp_value_m φ)⌝ₚ(⌜B⌝ₛ,⌜a⌝ₛ,q,Y,⌜A⌝ₛ)⟫

@[simp] theorem jp_local_closed_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (B a c A t X K H W : Term d)
    (hb : B.freeSupport = []) (ha : a.freeSupport = []) (hc' : c.freeSupport = []) (hA : A.freeSupport = [])
    (ht : t.freeSupport = []) (hx : X.freeSupport = []) (hk : K.freeSupport = [])
    (hh : H.freeSupport = []) (hw : W.freeSupport = []) : (jp_local_m φ B a c A t X K H W).FreeClosed := by
  simp -implicitDefEqProofs [jp_local_m,Definitional.Formula.FreeClosed,hc,hb,ha,hc',hA,ht,hx,hk,hh,hw]

theorem jp_local_delta_l {d} (φ : Formula 1 4) (B a c A t X K H W : Term d) :
    (jp_local_m φ B a c A t X K H W).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (kpair0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..)
      (.conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (jp_value_delta_l ..))))))))))

theorem jp_local_sat_l (hE : Extensional M) {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (ρ : Env M d)
    (B a c A t X K H W : Term d) : Formula.satisfies ρ (jp_local_m φ B a c A t X K H W) ↔
      Jp_local_d φ (B.eval ρ) (a.eval ρ) (c.eval ρ) (A.eval ρ) (t.eval ρ) (X.eval ρ) (K.eval ρ) (H.eval ρ) (W.eval ρ) := by
  simp only [jp_local_m,Jp_local_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    kpair0_sat_l hE,rd_entry0_sat_l hE,Formula.satisfies_mem_iff,jp_value_sat_l φ hc,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

/-- 单个原递归证书已覆盖整个方块边长，无须另选逐层证书。 -/
theorem ja_initial_certificate_l (hM : M.Models KPi) (S t : M.Domain) :
    ∃ D H W, Rc_cert_d ja_op_s (ja_env_l S) D H W ∧ M.mem t D := by
  obtain ⟨Y,value⟩ := ja_value_exists_l S hM t
  obtain ⟨W,D,H,cert,ht,_⟩ := (rc_value_sat_l (KPi.models_iff_l.mp hM).1.1 ja_op_s (ja_env_l S) t Y).mp value
  exact ⟨D,H,W,cert,ht⟩

theorem jp_local_iff_l {φ : Formula 1 4} {S B a c A t X η K D H W : M.Domain}
    (square : Oc_square_d t X η K) (cert : Rc_cert_d ja_op_s (ja_env_l S) D H W)
    (ht : M.mem t D) (hc : M.mem c η) :
    Jp_d I φ S B a c A ↔ Jp_local_d φ B a c A t X K H W := by
  constructor
  · rintro ⟨γ,q,Y,code,layer,base,param,index,members⟩
    obtain ⟨p,hp,pair,pc⟩ := (square.codes_l hZF γ q c).mp ⟨code,hc⟩
    obtain ⟨γ',hγ,q',hq,pair'⟩ := square.2.1.1 p hp
    obtain ⟨eγ,eq⟩ := kpair_injective_l M pair' pair
    subst γ' q'
    obtain ⟨Z,hZ,γZ⟩ := cert.function.2.1 γ (cert.hereditary t ht γ hγ)
    have value : Ja_value_d S γ Z := (rc_value_sat_l hZF.1 ..).mpr (cert.value_l γZ)
    have same := ja_value_unique_l S (ZF.models_kpi_l hZF) value layer.2
    subst Z
    exact ⟨p,hp,γ,hγ,q,hq,Y,hZ,pair,pc,γZ,base,param,index,
      (fun x hx => ((members x).mp hx).1),fun x hx => (members x).trans (and_iff_right hx)⟩
  · rintro ⟨p,hp,γ,hγ,q,_,Y,_,pair,pc,γY,base,param,index,values⟩
    have code := ((square.codes_l hZF γ q c).mpr ⟨p,hp,pair,pc⟩).1
    have layer : Ja_d S γ Y := ⟨square.1.mem hγ,(rc_value_sat_l hZF.1 ..).mpr (cert.value_l γY)⟩
    exact ⟨γ,q,Y,code,layer,base,param,index,fun x =>
      ⟨fun hx => ⟨values.1 x hx,(values.2 x (values.1 x hx)).mp hx⟩,fun h => (values.2 x h.1).mpr h.2⟩⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 固定实数参数下的唯一最小坏收益代码

非决定性使用同一模型的实际策略及对局量词。原对象公式分离坏代码，
序数最小性取得第一个代码；规范配对与层唯一性保证它只指向一个收益。
仅实数参数的存在性与带符号成员性见证分别由 PayoffRealWitness、PayoffSignedWitness 构造。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Jp_bad_d (J : kpair_convention_l.Interpretation M) (φ : Formula 1 4)
    (ω S B T a c : M.Domain) : Prop := ∃ A, Jp_d J φ S B a c A ∧ ¬ Det_d J ω B T A

def jp_bad_m {d} (φ : Formula 1 4) (ω S B T a c : Term d) : Formula 1 d :=
  .existsE (.conj (jp_m φ S.weaken B.weaken a.weaken c.weaken .newest)
    (.neg (det_m (𝒞 := kpair_convention_l) ω.weaken B.weaken T.weaken .newest)))

@[simp] theorem jp_bad_closed_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (ω S B T a c : Term d)
    (hw : ω.freeSupport = []) (hs : S.freeSupport = []) (hb : B.freeSupport = [])
    (ht : T.freeSupport = []) (ha : a.freeSupport = []) (hc' : c.freeSupport = []) :
    (jp_bad_m φ ω S B T a c).FreeClosed := by
  simp -implicitDefEqProofs [jp_bad_m,Definitional.Formula.FreeClosed,hw,hs,hb,ht,ha,hc',hc]

theorem jp_bad_sat_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (ρ : Env M d) (ω S B T a c : Term d) :
    Formula.satisfies ρ (jp_bad_m φ ω S B T a c) ↔
      Jp_bad_d I φ (ω.eval ρ) (S.eval ρ) (B.eval ρ) (T.eval ρ) (a.eval ρ) (c.eval ρ) := by
  simp only [jp_bad_m,Jp_bad_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    jp_sat_l hZF φ hc,Formula.satisfies_neg_iff,det_sat_l I hZF.1,Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]

def Jp_min_d (J : kpair_convention_l.Interpretation M) (φ : Formula 1 4)
    (ω S B T a c : M.Domain) : Prop := Jp_bad_d J φ ω S B T a c ∧
      ∀ d, M.mem d c → ¬ Jp_bad_d J φ ω S B T a d

def jp_min_m {d} (φ : Formula 1 4) (ω S B T a c : Term d) : Formula 1 d :=
  .conj (jp_bad_m φ ω S B T a c) (Formula.forallMem c
    (.neg (jp_bad_m φ ω.weaken S.weaken B.weaken T.weaken a.weaken .newest)))

@[simp] theorem jp_min_closed_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (ω S B T a c : Term d)
    (hw : ω.freeSupport = []) (hs : S.freeSupport = []) (hb : B.freeSupport = [])
    (ht : T.freeSupport = []) (ha : a.freeSupport = []) (hc' : c.freeSupport = []) :
    (jp_min_m φ ω S B T a c).FreeClosed := by
  simp -implicitDefEqProofs [jp_min_m,Definitional.Formula.FreeClosed,hw,hs,hb,ht,ha,hc',hc]

theorem jp_min_sat_l {d} (φ : Formula 1 4) (hc : φ.FreeClosed) (ρ : Env M d) (ω S B T a c : Term d) :
    Formula.satisfies ρ (jp_min_m φ ω S B T a c) ↔
      Jp_min_d I φ (ω.eval ρ) (S.eval ρ) (B.eval ρ) (T.eval ρ) (a.eval ρ) (c.eval ρ) := by
  simp only [jp_min_m,Jp_min_d,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_neg_iff,jp_bad_sat_l hZF φ hc,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem jp_min_l {φ : Formula 1 4} (hc : φ.FreeClosed) {ω S B T a c : M.Domain}
    (bad : Jp_bad_d I φ ω S B T a c) : ∃ d, Jp_min_d I φ ω S B T a d := by
  have ordinal : M.IsOrdinal c := bad.elim fun _ h => h.1.ordinal_l hZF
  let ρ : Env M 5 := ⟨fun i => [ω,S,B,T,a].get i,fun _ => ω⟩
  let ψ : UnarySchema 5 := {
    body := jp_bad_m φ (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) .newest
    freeClosed := jp_bad_closed_l φ hc _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl }
  have sat d : ψ.denote ρ d ↔ Jp_bad_d I φ ω S B T a d := jp_bad_sat_l hZF φ hc ..
  obtain ⟨d,_,yes,least⟩ := ZF.ordinal_min_l hZF ψ ρ ordinal ((sat c).mpr bad)
  exact ⟨d,(sat d).mp yes,fun e he h => least e he ((sat e).mpr h)⟩

theorem Jp_min_d.unique_l {φ ω S B T a c d}
    (left : Jp_min_d I φ ω S B T a c) (right : Jp_min_d I φ ω S B T a d) : c = d := by
  have co : M.IsOrdinal c := left.1.elim fun _ h => h.1.ordinal_l hZF
  have ho : M.IsOrdinal d := right.1.elim fun _ h => h.1.ordinal_l hZF
  rcases co.trichotomy hZF.1 ho (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) c d) with eq | cd | dc
  · exact hZF.1.eq_of_same_members c d eq
  · exact (right.2 c cd left.1).elim
  · exact (left.2 d dc right.1).elim

/-- 固定实数参数决定同一个最小坏收益；传递闭包和有限历史空间的呈示无关。 -/
theorem Jp_min_d.same_payoff_l {φ ω B a S S' T T' c d A D}
    (seed : Tc_d B S) (seed' : Tc_d B S')
    (finite : Fseq_space_d I ω ω T) (finite' : Fseq_space_d I ω ω T')
    (left : Jp_min_d I φ ω S B T a c) (right : Jp_min_d I φ ω S' B T' a d)
    (present : Jp_d I φ S B a c A) (present' : Jp_d I φ S' B a d D) : c = d ∧ A = D := by
  have eS : S' = S := tc_unique_l hZF.1 seed' seed
  have eT : T' = T := hZF.1.eq_of_same_members _ _ (fun t => (finite' t).trans (finite t).symm)
  subst S' T'
  have ec := left.unique_l hZF right
  subst d
  exact ⟨rfl,present.unique_l hZF present'⟩

/-- 从实际 L(ℝ) 收益的非决定性直接生成最小坏收益及其唯一性。 -/
theorem jp_min_payoff_l {ω B S T : M.Domain} (seed : Lr_seed_d hZF ω B S)
    (A : (la_model_l S (ZF.models_kpi_l hZF)).Domain) (sub : M.MemberSubset A.val B)
    (bad : ¬ Det_d I ω B T A.val) :
    ∃ a c D, M.mem a B ∧ Bc_binary_d ω a ∧ Jp_min_d I lr_payoff_m ω S B T a c ∧
      Jp_d I lr_payoff_m S B a c D ∧ ¬ Det_d I ω B T D ∧
      ∀ d E, Jp_min_d I lr_payoff_m ω S B T a d → Jp_d I lr_payoff_m S B a d E → E = D := by
  obtain ⟨a,c,real,binary,present⟩ := jp_presentation_l hZF seed A sub
  obtain ⟨d,least⟩ := jp_min_l hZF lr_payoff_closed_l ⟨A.val,present,bad⟩
  obtain ⟨D,define,no⟩ := least.1
  refine ⟨a,d,D,real,binary,least,define,no,fun e E other code => ?_⟩
  have eq := other.unique_l hZF least
  subst e
  exact code.unique_l hZF define

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 初段中全部收益的实际集合表

对每个原代码读取唯一收益；无合法呈示的代码取空收益。函数图由原定义
实际构造，完整覆盖每个更早合法代码。其有界核验和最小坏代码之前
每项决定性的证明由 PayoffTable 承接。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem jp_family_l (φ : Formula 1 4) (hc : φ.FreeClosed) (S B a c : M.Domain) :
    ∃ P F, M.IsPowerSetOf P B ∧ Fn0_d c P F ∧
      (∀ d, M.mem d c → ∀ A, Jp_d I φ S B a d A → Rd_entry_d d A F) ∧
      ∀ d A, Rd_entry_d d A F → Jp_d I φ S B a d A ∨ (∀ y, ¬ M.mem y A) := by
  obtain ⟨e,empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨P,power⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 4 := ⟨fun i => [S,B,a,e].get i,fun _ => e⟩
  let ψ : BinarySchema 4 := {
    body := set[6] ⟪
      ⌜(jp_m φ)⌝ₚ(⌜(.bound 2 : Term 6)⌝ₛ,⌜(.bound 3 : Term 6)⌝ₛ,⌜(.bound 4 : Term 6)⌝ₛ,
        ⌜(.bound 1 : Term 6)⌝ₛ,⌜(.newest : Term 6)⌝ₛ) ∨
      ((¬ (∃ A, ⌜(jp_m φ)⌝ₚ(⌜(.bound 2 : Term 6)⌝ₛ,⌜(.bound 3 : Term 6)⌝ₛ,⌜(.bound 4 : Term 6)⌝ₛ,
        ⌜(.bound 1 : Term 6)⌝ₛ,A))) ∧ ⌜(.newest : Term 6)⌝ₛ = ⌜(.bound 5 : Term 6)⌝ₛ)⟫
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,hc] }
  have sat d A : ψ.denote ρ d A ↔ Jp_d I φ S B a d A ∨
      (¬ (∃ D, Jp_d I φ S B a d D)) ∧ A = e := by
    simp only [ψ,BinarySchema.denote,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
      jp_sat_l hZF φ hc,Formula.satisfies_neg_iff,Formula.satisfies_exists_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Definitional.Term.eval_weaken]
    rfl
  have total d : ∃ A, ψ.denote ρ d A := by
    classical
    by_cases h : ∃ A, Jp_d I φ S B a d A
    · obtain ⟨A,hA⟩ := h
      exact ⟨A,(sat d A).mpr (Or.inl hA)⟩
    · exact ⟨e,(sat d e).mpr (Or.inr ⟨h,rfl⟩)⟩
  have unique d A D (hA : ψ.denote ρ d A) (hD : ψ.denote ρ d D) : A = D := by
    rcases (sat d A).mp hA with codeA | ⟨none,rfl⟩ <;> rcases (sat d D).mp hD with codeD | ⟨none',rfl⟩
    · exact codeA.unique_l hZF codeD
    · exact (none' ⟨A,codeA⟩).elim
    · exact (none ⟨D,codeD⟩).elim
    · rfl
  have bounded d A (hA : ψ.denote ρ d A) : M.mem A P := by
    apply (power A).mpr
    rcases (sat d A).mp hA with ⟨_,_,_,_,_,_,_,_,members⟩ | ⟨_,rfl⟩
    · exact fun y hy => ((members y).mp hy).1
    · exact fun y hy => (empty y hy).elim
  obtain ⟨F,fn,edges⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ ρ (source := c) (target := P)
    (fun d _ => total d) (fun d _ => unique d) (fun d A _ => bounded d A)
  refine ⟨P,F,power,fn0_of_function_l (ZF.modelsKP hZF) fn,
    fun d hd A hA => (edges d A).mpr ⟨hd,(sat d A).mpr (Or.inl hA)⟩,?_⟩
  intro d A edge
  rcases (sat d A).mp ((edges d A).mp edge).2 with code | ⟨_,eq⟩
  · exact Or.inl code
  · exact Or.inr (fun y hy => empty y (eq ▸ hy))

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 派生模型中最小坏代码的原公式

先在原模型内量化完整博弈基础数据，再将同一公式相对化到实际 Jensen
并类。自由槽只有实数族、指定实数和代码；代码保留为字面参数，
不借任意成员见证的坍塌固定高序数。规范基础数据唯一性保证代码唯一。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Jm_d (J : kpair_convention_l.Interpretation M) (φ : Formula 1 4) (B a c : M.Domain) : Prop :=
  M.mem a B ∧ ∃ ω S T, Baire_d J ω B ∧ Tc_d B S ∧ Fseq_space_d J ω ω T ∧ Jp_min_d J φ ω S B T a c

def jm_m (φ : Formula 1 4) : Formula 1 3 :=
  .conj (.mem (.bound 1) (.bound 0)) (.existsE (.existsE (.existsE
    (.conj (baire_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 3))
      (.conj (tc_m (.bound 3) (.bound 1))
        (.conj (fseq_space_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 2) (.bound 0))
          (jp_min_m φ (.bound 2) (.bound 1) (.bound 3) (.bound 0) (.bound 4) (.bound 5))))))))

theorem jm_closed_l {φ : Formula 1 4} (hc : φ.FreeClosed) : (jm_m φ).FreeClosed := by
  simp -implicitDefEqProofs [jm_m,Definitional.Formula.FreeClosed,hc]

theorem jm_sat_l (φ : Formula 1 4) (hc : φ.FreeClosed) (ρ : Env M 3) :
    Formula.satisfies ρ (jm_m φ) ↔ Jm_d I φ (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) := by
  simp only [jm_m,Jm_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,
    baire_sat_l I hZF.1,tc_sat_l,fseq_space_sat_l I hZF.1,jp_min_sat_l hZF φ hc]
  rfl

theorem Jm_d.ordinal_l {φ B a c} (h : Jm_d I φ B a c) : M.IsOrdinal c := by
  obtain ⟨_,_,_,_,_,_,_,⟨A,present,_⟩,_⟩ := h
  exact present.ordinal_l hZF

theorem Jm_d.unique_l {φ B a c d} (left : Jm_d I φ B a c) (right : Jm_d I φ B a d) : c = d := by
  obtain ⟨_,ω,S,T,space,tc,finite,least⟩ := left
  obtain ⟨_,v,U,V,space',tc',finite',least'⟩ := right
  have ev : v = ω := hZF.1.eq_of_same_members v ω (fun n =>
    ⟨space'.1.2 ω space.1.1 n,space.1.2 v space'.1.1 n⟩)
  have eS := tc_unique_l hZF.1 tc' tc
  subst v U
  have eT : V = T := hZF.1.eq_of_same_members V T (fun s => (finite' s).trans (finite s).symm)
  subst V
  exact least.unique_l hZF least'

def Dm_min_d (φ : Formula 1 4) (B a c : M.Domain) : Prop :=
  ∃ S, ∃ tc : Tc_d B S,
    let D := la_model_l S (ZF.models_kpi_l hZF)
    let hD := la_model_zf_l S hZF tc.1
    ∃ b x q : D.Domain, b.val = B ∧ x.val = a ∧ q.val = c ∧ Jm_d (kp_pair_l (ZF.modelsKP hD)) φ b x q

def dm_min_m (φ : Formula 1 4) : Formula 1 3 := .existsE
  (.conj (tc_m (.bound 1) .newest) (.conj (la_m .newest (.bound 2))
    (.conj (la_m .newest (.bound 3)) (la_rel_m (jm_m φ) .newest (fun i => .bound i.succ)))))

theorem dm_min_closed_l {φ : Formula 1 4} (hc : φ.FreeClosed) : (dm_min_m φ).FreeClosed := by
  simp only [dm_min_m,Definitional.Formula.FreeClosed]
  exact ⟨tc_m_freeClosed _ _ rfl rfl,la_m_freeClosed _ _ rfl rfl,la_m_freeClosed _ _ rfl rfl,
    la_rel_closed_l _ (jm_closed_l hc) _ _ rfl (fun _ => rfl)⟩

theorem dm_min_sat_l (φ : Formula 1 4) (hc : φ.FreeClosed) (ρ : Env M 3) :
    Formula.satisfies ρ (dm_min_m φ) ↔ Dm_min_d hZF φ (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) := by
  simp only [dm_min_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,tc_sat_l,la_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨S,tc,ha,hc',truth⟩
    let D := la_model_l S (ZF.models_kpi_l hZF)
    have hD : D.Models ZF := la_model_zf_l S hZF tc.1
    let b : D.Domain := ⟨ρ.bound 0,la_transitive_l S (ZF.models_kpi_l hZF) tc.1 (la_seed_l S (ZF.models_kpi_l hZF)) tc.2.1⟩
    let a : D.Domain := ⟨ρ.bound 1,ha⟩
    let c : D.Domain := ⟨ρ.bound 2,hc'⟩
    let η : Env D 3 := ⟨fun i => [b,a,c].get i,fun _ => b⟩
    refine ⟨S,tc,b,a,c,rfl,rfl,rfl,(jm_sat_l hD φ hc η).mp ?_⟩
    exact (la_rel_sat_l (ZF.models_kpi_l hZF) S tc.1 (jm_m φ) (jm_closed_l hc) η (ρ.push S) .newest
      (fun i => .bound i.succ) rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp truth
  · rintro ⟨S,tc,b,a,c,eb,ea,ec,least⟩
    let D := la_model_l S (ZF.models_kpi_l hZF)
    have hD : D.Models ZF := la_model_zf_l S hZF tc.1
    let η : Env D 3 := ⟨fun i => [b,a,c].get i,fun _ => b⟩
    exact ⟨S,tc,(show La_d S (ρ.bound 1) from ea ▸ a.property),(show La_d S (ρ.bound 2) from ec ▸ c.property),
      (la_rel_sat_l (ZF.models_kpi_l hZF) S tc.1 (jm_m φ) (jm_closed_l hc) η (ρ.push S) .newest
        (fun i => .bound i.succ) rfl
        (Fin.cases eb.symm (Fin.cases ea.symm (Fin.cases ec.symm (fun i => Fin.elim0 i))))).mpr
        ((jm_sat_l hD φ hc η).mpr least)⟩

/-- 固定实际种子后，原外层公式准确读取该派生模型中的同一个代码参数。 -/
theorem dm_min_model_l {B S : M.Domain} (tc : Tc_d B S) (φ : Formula 1 4)
    (b a c : (la_model_l S (ZF.models_kpi_l hZF)).Domain) (eb : b.val = B) :
    Dm_min_d hZF φ B a.val c.val ↔
      Jm_d (kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF tc.1))) φ b a c := by
  constructor
  · rintro ⟨T,tc',b',a',c',eb',ea,ec,least⟩
    have eS := tc_unique_l hZF.1 tc' tc
    subst T
    have eB : b' = b := Subtype.ext (eb'.trans eb.symm)
    have eA : a' = a := Subtype.ext ea
    have eC : c' = c := Subtype.ext ec
    simpa only [eB,eA,eC] using least
  · exact fun least => ⟨S,tc,b,a,c,eb,rfl,rfl,least⟩

theorem Dm_min_d.ordinal_l {φ B a c} (h : Dm_min_d hZF φ B a c) : M.IsOrdinal c := by
  obtain ⟨S,tc,b,a',q,_,_,eq,least⟩ := h
  have hD := la_model_zf_l S hZF tc.1
  let ρ : Env (la_model_l S (ZF.models_kpi_l hZF)) 1 := ⟨fun _ => q,fun _ => q⟩
  have native := (KP.ord0_sat_l (ZF.modelsKP hD) ρ .newest).mpr (least.ordinal_l hD)
  have raw := (KP.ord0_sat_l (ZF.modelsKP hZF) _ .newest).mp
    ((la_model_delta_l S (ZF.models_kpi_l hZF) tc.1 (KP.ord0_delta_l .newest) ρ).mp native)
  exact eq ▸ raw

theorem Dm_min_d.real_l {φ B a c} (h : Dm_min_d hZF φ B a c) : M.mem a B := by
  obtain ⟨_,_,b,x,_,eb,ex,_,least⟩ := h
  have real : M.mem x.val b.val := least.1
  simpa only [eb,ex] using real

theorem Dm_min_d.unique_l {φ B a c d} (left : Dm_min_d hZF φ B a c) (right : Dm_min_d hZF φ B a d) : c = d := by
  obtain ⟨S,tc,b,x,q,eb,ex,eq,least⟩ := left
  obtain ⟨T,tc',b',x',q',eb',ex',eq',least'⟩ := right
  have eS := tc_unique_l hZF.1 tc' tc
  subst T
  have eB : b' = b := Subtype.ext (eb'.trans eb.symm)
  have eX : x' = x := Subtype.ext (ex'.trans ex.symm)
  subst b' x'
  exact eq.symm.trans ((congrArg Subtype.val (least.unique_l (la_model_zf_l S hZF tc.1) least')).trans eq')

end YesMetaZFC.SetTheory.InnerModel.Relative
