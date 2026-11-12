import YesMetaZFC.Model.Forcing.Ground.RealCodeImage
import YesMetaZFC.Model.SetTheory.LevyReflection.Arguments
import YesMetaZFC.Model.SetTheory.Embedding.AttemptRelative
import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffQuerySound
import YesMetaZFC.Model.Forcing.Truth.ClosedTruth
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism
import YesMetaZFC.Model.Forcing.Embedding.Rank

/-! # 有限名字检查读取原源模型自己的力迫关系

根条件只需在给定基准条件的检查名字之下迫使函数性。数字检查断言指定条件
迫使同一名字含有该图边；两者都由相对化公式表达，不改用背景的力迫关系。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u

def nr_base0_m : Formula 1 6 := set[6] ⟪∃ t,
  ⌜check_m⌝ₚ(⌜(.bound 3 : Term 6)⌝ₛ,⌜(.bound 2 : Term 6)⌝ₛ,t) ∧
  ⌜fn_name_m⌝ₚ(⌜(.bound 0 : Term 6)⌝ₛ,⌜(.bound 1 : Term 6)⌝ₛ,⌜(.bound 0 : Term 6)⌝ₛ,
    ⌜(.bound 5 : Term 6)⌝ₛ,t,t,⌜(.bound 4 : Term 6)⌝ₛ)⟫

@[simp] theorem nr_base0_closed_l : nr_base0_m.FreeClosed := by
  simp -implicitDefEqProofs [nr_base0_m,Definitional.Formula.FreeClosed]

theorem nr_base_native_l {N : Structure.{u}} (hN : Extensional N) (ρ : Env N 6) :
    Formula.satisfies ρ nr_base0_m ↔ ∃ t, Check_d N (ρ.bound 3) (ρ.bound 2) t ∧
      Fn_name_d N (ρ.bound 0) (ρ.bound 1) (ρ.bound 0) (ρ.bound 5) t t (ρ.bound 4) := by
  simp only [nr_base0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,check_sat_l N hN,fn_name_sat_l hN]
  rfl

def nr_base_m {n} (X Q T ω b τ p : Term n) : Formula 1 n :=
  lr_rel_m nr_base0_m X (fun i => [Q,T,ω,b,τ,p].get i)

def nr_edge_m {n} (X Q T b τ i y p : Term n) : Formula 1 n :=
  lr_rel_m nentry0_m X (fun j => [Q,T,Q,b,τ,i,y,p].get j)

theorem nr_base_delta_l {n} (X Q T ω b τ p : Term n) : (nr_base_m X Q T ω b τ p).IsDelta0 := lr_rel_delta_l ..
theorem nr_edge_delta_l {n} (X Q T b τ i y p : Term n) : (nr_edge_m X Q T b τ i y p).IsDelta0 := lr_rel_delta_l ..

@[simp] theorem nr_base_closed_l {n} (X Q T ω b τ p : Term n)
    (hX : X.freeSupport = []) (hQ : Q.freeSupport = []) (hT : T.freeSupport = [])
    (hw : ω.freeSupport = []) (hb : b.freeSupport = []) (hτ : τ.freeSupport = []) (hp : p.freeSupport = []) :
    (nr_base_m X Q T ω b τ p).FreeClosed :=
  lr_rel_closed_l _ nr_base0_closed_l _ _ hX
    (Fin.cases hQ (Fin.cases hT (Fin.cases hw (Fin.cases hb (Fin.cases hτ (Fin.cases hp (fun k => Fin.elim0 k)))))))

@[simp] theorem nr_edge_closed_l {n} (X Q T b τ i y p : Term n)
    (hX : X.freeSupport = []) (hQ : Q.freeSupport = []) (hT : T.freeSupport = []) (hb : b.freeSupport = [])
    (hτ : τ.freeSupport = []) (hi : i.freeSupport = []) (hy : y.freeSupport = []) (hp : p.freeSupport = []) :
    (nr_edge_m X Q T b τ i y p).FreeClosed :=
  lr_rel_closed_l _ nentry0_closed_l _ _ hX
    (Fin.cases hQ (Fin.cases hT (Fin.cases hQ (Fin.cases hb (Fin.cases hτ
      (Fin.cases hi (Fin.cases hy (Fin.cases hp (fun k => Fin.elim0 k)))))))))

def Nr_base_d {M : Structure.{u}} (X Q T ω b τ p : M.Domain) : Prop :=
  Formula.satisfies (⟨fun i => [X,Q,T,ω,b,τ,p].get i,fun _ => X⟩ : Env M 7)
    (nr_base_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6))

def Nr_edge_d {M : Structure.{u}} (X Q T b τ i y p : M.Domain) : Prop :=
  Formula.satisfies (⟨fun j => [X,Q,T,b,τ,i,y,p].get j,fun _ => X⟩ : Env M 8)
    (nr_edge_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7))

theorem nr_base_sat_l {M : Structure.{u}} {n} (ρ : Env M n) (X Q T ω b τ p : Term n) :
    Formula.satisfies ρ (nr_base_m X Q T ω b τ p) ↔
      Nr_base_d (X.eval ρ) (Q.eval ρ) (T.eval ρ) (ω.eval ρ) (b.eval ρ) (τ.eval ρ) (p.eval ρ) :=
  lr_rel_arguments_l _ nr_base0_closed_l _ _ _ _ _ _ rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))

theorem nr_edge_sat_l {M : Structure.{u}} {n} (ρ : Env M n) (X Q T b τ i y p : Term n) :
    Formula.satisfies ρ (nr_edge_m X Q T b τ i y p) ↔
      Nr_edge_d (X.eval ρ) (Q.eval ρ) (T.eval ρ) (b.eval ρ) (τ.eval ρ) (i.eval ρ) (y.eval ρ) (p.eval ρ) :=
  lr_rel_arguments_l _ nentry0_closed_l _ _ _ _ _ _ rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))

variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) {c X R : M.Domain}
  (source : Smem_d I c X R) (trans : M.TransitiveSet X)
include trans
local notation "N" => smdl_structure_l I (R := R) (And.left (And.right (And.left source)))

theorem nr_base_read_l (hN : Extensional N) (Q T ω b τ p : (N).Domain) :
    Nr_base_d X Q.val T.val ω.val b.val τ.val p.val ↔ ∃ t, Check_d N b ω t ∧ Fn_name_d N Q T Q p t t τ := by
  let ρ : Env N 6 := ⟨fun i => [Q,T,ω,b,τ,p].get i,fun _ => Q⟩
  apply (lr_rel_decode_l I source.1 source.2 trans nr_base0_m nr_base0_closed_l ρ _ _ _ rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))).trans
  exact nr_base_native_l hN ρ

theorem nr_edge_read_l (hN : Extensional N) (Q T b τ i y p : (N).Domain) :
    Nr_edge_d X Q.val T.val b.val τ.val i.val y.val p.val ↔ Nentry_d Q T Q b τ i y p := by
  let ρ : Env N 8 := ⟨fun j => [Q,T,Q,b,τ,i,y,p].get j,fun _ => Q⟩
  exact (lr_rel_decode_l I source.1 source.2 trans nentry0_m nentry0_closed_l ρ _ _ _ rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))).trans
    (nentry_sat_l hN ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7))

/-- 原条件列中的加强仍判定同一条名字图边。 -/
theorem nr_edge_strengthen_l (native : (N).Models ZF) (Q T b τ i y p r : (N).Domain)
    (O : Cond_order_d N Q T Q) (hb : (N).mem b Q) (name : Name_d N Q τ)
    (hp : (N).mem p Q) (below : Below_d N Q T Q r p)
    (edge : Nr_edge_d X Q.val T.val b.val τ.val i.val y.val p.val) :
    Nr_edge_d X Q.val T.val b.val τ.val i.val y.val r.val := by
  obtain ⟨s,t,cs,ct,force⟩ := (nr_edge_read_l I source trans native.1 Q T b τ i y p).mp edge
  exact (nr_edge_read_l I source trans native.1 Q T b τ i y r).mpr ⟨s,t,cs,ct,
    (rel_force_regular_l O native name (check_name_l N (check_range_l N native) hb cs)
      (check_name_l N (check_range_l N native) hb ct)).1 p r hp below force⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 固定名字位置与逐位判值期限的有限检查

v、w 是两个常值位置列，分别选择基准条件和实数名字。u(i) 指定判值条件
在原条件列 f 中的位置。所有涉及的位置可见时才检查，因而严格保持前缀。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}}

structure Nr_at_d (ω X Q T n e f x u v w : M.Domain) : Prop where
  base_index : ∀ i j a b, M.mem i n → M.mem j n → Rd_entry_d i a v → Rd_entry_d j b v → a = b
  name_index : ∀ i j a b, M.mem i n → M.mem j n → Rd_entry_d i a w → Rd_entry_d j b w → a = b
  root : ∀ o a b p h τ, M.mem o n → M.mem a n → M.mem b n → (∀ y, ¬ M.mem y o) →
    Rd_entry_d o a v → Rd_entry_d o b w → Rd_entry_d a h e → Rd_entry_d b τ e → Rd_entry_d o p f →
      M.mem h Q ∧ Rd_entry_d p h T ∧ Nr_base_d X Q T ω h τ p
  digits : ∀ i k a b y p h τ, M.mem i n → M.mem k n → M.mem a n → M.mem b n →
    Rd_entry_d i y x → Rd_entry_d i k u → Rd_entry_d k p f → Rd_entry_d i a v → Rd_entry_d i b w →
    Rd_entry_d a h e → Rd_entry_d b τ e → Nr_edge_d X Q T h τ i y p

def nr_at_m {d} (ω X Q T n e f x u v w : Term d) : Formula 1 d :=
  .conj (set[d] ⟪∀ i j a b, i ∈ ⌜n⌝ₛ → j ∈ ⌜n⌝ₛ →
    ⌜rd_entry0_m⌝ₚ(i,a,⌜v⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j,b,⌜v⌝ₛ) → a = b⟫)
  (.conj (set[d] ⟪∀ i j a b, i ∈ ⌜n⌝ₛ → j ∈ ⌜n⌝ₛ →
    ⌜rd_entry0_m⌝ₚ(i,a,⌜w⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j,b,⌜w⌝ₛ) → a = b⟫)
  (.conj (set[d] ⟪∀ o a b p h τ, o ∈ ⌜n⌝ₛ → a ∈ ⌜n⌝ₛ → b ∈ ⌜n⌝ₛ → ⌜Formula.isEmpty⌝ₚ(o) →
    ⌜rd_entry0_m⌝ₚ(o,a,⌜v⌝ₛ) → ⌜rd_entry0_m⌝ₚ(o,b,⌜w⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(a,h,⌜e⌝ₛ) → ⌜rd_entry0_m⌝ₚ(b,τ,⌜e⌝ₛ) → ⌜rd_entry0_m⌝ₚ(o,p,⌜f⌝ₛ) →
      h ∈ ⌜Q⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(p,h,⌜T⌝ₛ) ∧ ⌜nr_base_m⌝ₚ(⌜X⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,⌜ω⌝ₛ,h,τ,p)⟫)
  (set[d] ⟪∀ i k a b y p h τ, i ∈ ⌜n⌝ₛ → k ∈ ⌜n⌝ₛ → a ∈ ⌜n⌝ₛ → b ∈ ⌜n⌝ₛ →
    ⌜rd_entry0_m⌝ₚ(i,y,⌜x⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i,k,⌜u⌝ₛ) → ⌜rd_entry0_m⌝ₚ(k,p,⌜f⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(i,a,⌜v⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i,b,⌜w⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(a,h,⌜e⌝ₛ) → ⌜rd_entry0_m⌝ₚ(b,τ,⌜e⌝ₛ) →
      ⌜nr_edge_m⌝ₚ(⌜X⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,h,τ,i,y,p)⟫)))
derive_free_closed nr_at_m

theorem nr_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X Q T n e f x u v w : Term d) :
    Formula.satisfies ρ (nr_at_m ω X Q T n e f x u v w) ↔
      Nr_at_d (ω.eval ρ) (X.eval ρ) (Q.eval ρ) (T.eval ρ) (n.eval ρ) (e.eval ρ) (f.eval ρ)
        (x.eval ρ) (u.eval ρ) (v.eval ρ) (w.eval ρ) := by
  simp only [nr_at_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_isEmpty_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    rd_entry0_sat_l hE,nr_base_sat_l,nr_edge_sat_l,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d⟩ => ⟨a,b,c,d⟩,fun h => ⟨h.base_index,h.name_index,h.root,h.digits⟩⟩

theorem Nr_at_d.prefix_l {ω X Q T n m e f x u v w e' f' x' u' v' w' : M.Domain}
    (h : Nr_at_d ω X Q T m e f x u v w) (sub : M.MemberSubset n m)
    (ee : M.MemberSubset e' e) (ff : M.MemberSubset f' f) (xx : M.MemberSubset x' x)
    (uu : M.MemberSubset u' u) (vv : M.MemberSubset v' v) (ww : M.MemberSubset w' w) :
    Nr_at_d ω X Q T n e' f' x' u' v' w' := by
  have move {A B i y : M.Domain} (sub : M.MemberSubset A B) (iy : Rd_entry_d i y A) : Rd_entry_d i y B :=
    iy.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  exact ⟨fun i j a b hi hj ia jb => h.base_index i j a b (sub i hi) (sub j hj) (move vv ia) (move vv jb),
    fun i j a b hi hj ia jb => h.name_index i j a b (sub i hi) (sub j hj) (move ww ia) (move ww jb),
    fun o a b p q τ ho ha hb empty oa ob aq bτ op => h.root o a b p q τ
      (sub o ho) (sub a ha) (sub b hb) empty (move vv oa) (move ww ob) (move ee aq) (move ee bτ) (move ff op),
    fun i k a b y p q τ hi hk ha hb iy ik kp ia ib aq bτ => h.digits i k a b y p q τ
      (sub i hi) (sub k hk) (sub a ha) (sub b hb) (move xx iy) (move uu ik) (move ff kp)
      (move vv ia) (move ww ib) (move ee aq) (move ee bτ)⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 四个所需位置均有内部自然数界，每项数字检查都在同一有限节点实际发生。 -/
theorem nr_branch_l {ω X Q T e f x u v w : M.Domain} (hw : M.IsOmega ω)
    (prefixes : ∀ n, M.mem n ω → ∃ e' f' x' u' v' w', Nr_at_d ω X Q T n e' f' x' u' v' w' ∧
      M.IsRestrictionOf I e' e n ∧ M.IsRestrictionOf I f' f n ∧ M.IsRestrictionOf I x' x n ∧
      M.IsRestrictionOf I u' u n ∧ M.IsRestrictionOf I v' v n ∧ M.IsRestrictionOf I w' w n) :
    Nr_at_d ω X Q T ω e f x u v w := by
  have upper a b c d (ha : M.mem a ω) (hb : M.mem b ω) (hc : M.mem c ω) (hd : M.mem d ω) :
      ∃ n, M.mem n ω ∧ M.mem a n ∧ M.mem b n ∧ M.mem c n ∧ M.mem d n := by
    obtain ⟨k,hk,ak,bk⟩ := at_upper_l hZF hw ha hb
    obtain ⟨l,hl,cl,dl⟩ := at_upper_l hZF hw hc hd
    obtain ⟨n,hn,kn,ln⟩ := at_upper_l hZF hw hk hl
    have nt := (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive
    exact ⟨n,hn,nt k kn a ak,nt k kn b bk,nt l ln c cl,nt l ln d dl⟩
  constructor
  · intro i j a b hi hj ia jb
    obtain ⟨n,hn,hin,hjn⟩ := at_upper_l hZF hw hi hj
    obtain ⟨_,_,_,_,_,_,check,_,_,_,_,cv,_⟩ := prefixes n hn
    exact check.base_index i j a b hin hjn ((cv.2 i a).mpr ⟨hin,ia⟩) ((cv.2 j b).mpr ⟨hjn,jb⟩)
  · intro i j a b hi hj ia jb
    obtain ⟨n,hn,hin,hjn⟩ := at_upper_l hZF hw hi hj
    obtain ⟨_,_,_,_,_,_,check,_,_,_,_,_,cw⟩ := prefixes n hn
    exact check.name_index i j a b hin hjn ((cw.2 i a).mpr ⟨hin,ia⟩) ((cw.2 j b).mpr ⟨hjn,jb⟩)
  · intro o a b p q τ ho ha hb empty oa ob aq bτ op
    obtain ⟨n,hn,on,an,bn,_⟩ := upper o a b o ho ha hb ho
    obtain ⟨_,_,_,_,_,_,check,ce,cf,_,_,cv,cw⟩ := prefixes n hn
    exact check.root o a b p q τ on an bn empty ((cv.2 o a).mpr ⟨on,oa⟩) ((cw.2 o b).mpr ⟨on,ob⟩)
      ((ce.2 a q).mpr ⟨an,aq⟩) ((ce.2 b τ).mpr ⟨bn,bτ⟩) ((cf.2 o p).mpr ⟨on,op⟩)
  · intro i k a b y p q τ hi hk ha hb iy ik kp ia ib aq bτ
    obtain ⟨n,hn,hin,hkn,an,bn⟩ := upper i k a b hi hk ha hb
    obtain ⟨_,_,_,_,_,_,check,ce,cf,cx,cu,cv,cw⟩ := prefixes n hn
    exact check.digits i k a b y p q τ hin hkn an bn ((cx.2 i y).mpr ⟨hin,iy⟩) ((cu.2 i k).mpr ⟨hin,ik⟩)
      ((cf.2 k p).mpr ⟨hkn,kp⟩) ((cv.2 i a).mpr ⟨hin,ia⟩) ((cw.2 i b).mpr ⟨hin,ib⟩)
      ((ce.2 a q).mpr ⟨an,aq⟩) ((ce.2 b τ).mpr ⟨bn,bτ⟩)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 固定地实数参数及原查询名字的正负力迫

ω 与指定实数参数使用同一个已接受基准的检查名字；查询名字和规范实数并
名字保持原对象。真值定理双向连接实际派生见证与原泛型接受的条件。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.InnerModel.Relative
universe u
variable {M : Structure.{u}}

def Qs_force_d (φ : Formula 1 4) (sign : Bool) (Q T r ω a τ b p : M.Domain) : Prop := ∃ s t,
  Check_d M b ω s ∧ Check_d M b a t ∧
    Forces_d M Q T Q (dq_signed_m φ sign) (⟨fun i => [r,s,t,τ].get i,fun _ => r⟩ : Env M 4) p

def qs_force_m {n} (φ : Formula 1 4) (sign : Bool) (Q T r ω a τ b p : Term n) : Formula 1 n := .existsE (.existsE
  (.conj (check_m b.weaken.weaken ω.weaken.weaken (.bound 1))
    (.conj (check_m b.weaken.weaken a.weaken.weaken .newest)
      (force_at_m (dq_signed_m φ sign) (fun i => [r.weaken.weaken,.bound 1,.newest,τ.weaken.weaken].get i)
        Q.weaken.weaken T.weaken.weaken Q.weaken.weaken p.weaken.weaken))))

theorem qs_force_closed_l {n} {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool) (Q T r ω a τ b p : Term n)
    (hQ : Q.freeSupport = []) (hT : T.freeSupport = []) (hr : r.freeSupport = []) (hw : ω.freeSupport = [])
    (ha : a.freeSupport = []) (hτ : τ.freeSupport = []) (hb : b.freeSupport = []) (hp : p.freeSupport = []) :
    (qs_force_m φ sign Q T r ω a τ b p).FreeClosed := by
  simp only [qs_force_m,Definitional.Formula.FreeClosed]
  refine ⟨check_m_freeClosed _ _ _ (by simpa using hb) (by simpa using hw) rfl,
    check_m_freeClosed _ _ _ (by simpa using hb) (by simpa using ha) rfl,
    force_at_closed_l _ _ _ _ _ _ (dq_signed_closed_l hc sign) ?_
      (by simpa using hQ) (by simpa using hT) (by simpa using hQ) (by simpa using hp)⟩
  intro i
  refine Fin.cases ?_ (Fin.cases rfl (Fin.cases rfl (Fin.cases ?_ (fun i => Fin.elim0 i)))) i
  · change (r.weaken.weaken).freeSupport = []
    simpa using hr
  · change (τ.weaken.weaken).freeSupport = []
    simpa using hτ

theorem qs_force_sat_l (hE : Extensional M) {n} {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool)
    (ρ : Env M n) (Q T r ω a τ b p : Term n) :
    Formula.satisfies ρ (qs_force_m φ sign Q T r ω a τ b p) ↔
      Qs_force_d φ sign (Q.eval ρ) (T.eval ρ) (r.eval ρ) (ω.eval ρ) (a.eval ρ) (τ.eval ρ) (b.eval ρ) (p.eval ρ) := by
  simp only [qs_force_m,Qs_force_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    check_sat_l M hE,force_at_sat_l,Definitional.Term.eval_weaken]
  apply exists_congr; intro s
  apply exists_congr; intro t
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forces_env_l hE _ (dq_signed_closed_l hc sign)
  intro i
  refine Fin.cases ?_ (Fin.cases rfl (Fin.cases rfl (Fin.cases ?_ (fun i => Fin.elim0 i)))) i
  · change (r.weaken.weaken).eval ((ρ.push s).push t) = r.eval ρ
    simp only [Definitional.Term.eval_weaken]
  · change (τ.weaken.weaken).eval ((ρ.push s).push t) = τ.eval ρ
    simp only [Definitional.Term.eval_weaken]

variable (hZF : M.Models ZF) {Q T : M.Domain} (O : Cond_order_d M Q T Q)
include hZF O

omit hZF O in
/-- 源模型同构沿同一参数搬运正负力迫；查询名字和被接受条件均不重选。 -/
theorem Qs_force_d.image_l {N : Structure} (hM : Extensional M) (hN : Extensional N)
    (e : M.Domain → N.Domain) (elem : Pe_d e) {φ : Formula 1 4} (hc : φ.FreeClosed)
    {sign : Bool} {Q T r ω a τ b p : M.Domain} (force : Qs_force_d φ sign Q T r ω a τ b p) :
    Qs_force_d φ sign (e Q) (e T) (e r) (e ω) (e a) (e τ) (e b) (e p) := by
  obtain ⟨s,t,cs,ct,forced⟩ := force
  refine ⟨e s,e t,(em_check_l hM hN e elem).mp cs,(em_check_l hM hN e elem).mp ct,?_⟩
  have moved := (em_forces_l e elem _ (dq_signed_closed_l hc sign)
    (⟨fun i => [r,s,t,τ].get i,fun _ => r⟩ : Env M 4) Q T Q p).mp forced
  exact (forces_env_l hN _ (dq_signed_closed_l hc sign) _ _
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) _).mp moved

theorem Qs_force_d.strengthen_l {φ : Formula 1 4} (hc : φ.FreeClosed) {sign : Bool} {r ω a τ b p q : M.Domain}
    (h : Qs_force_d φ sign Q T r ω a τ b p) (hb : M.mem b Q) (hr : Name_d M Q r) (hτ : Name_d M Q τ)
    (hp : M.mem p Q) (below : Below_d M Q T Q q p) : Qs_force_d φ sign Q T r ω a τ b q := by
  obtain ⟨s,t,cs,ct,force⟩ := h
  let ρ : Env M 4 := ⟨fun i => [r,s,t,τ].get i,fun _ => r⟩
  have names : ∀ i, Name_d M Q (ρ.bound i) := Fin.cases hr
    (Fin.cases (check_name_l M (check_range_l M hZF) hb cs)
      (Fin.cases (check_name_l M (check_range_l M hZF) hb ct) (Fin.cases hτ (fun i => Fin.elim0 i))))
  exact ⟨s,t,cs,ct,(forces_closed_regular_l O hZF _ (dq_signed_closed_l hc sign) ρ names).1 p q hp below force⟩

variable {G : M.Domain → Prop} (generic : Generic_d M Q T Q G)
include generic
local notation "E" => extension_l M hZF Q T Q G

theorem qs_truth_l {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool) {r ω a τ b : M.Domain} (hb : G b)
    (j : M.Domain → (E).Domain) (ground : ∀ z, Gval_d M Q T Q G z (j z))
    {Z x : (E).Domain} (value : Qval_d M Q T Q G r Z) (query : Qval_d M Q T Q G τ x) :
    (∃ p, G p ∧ Qs_force_d φ sign Q T r ω a τ b p) ↔
      Dq_signed_d (kp_pair_l (ZF.modelsKP (preserves_zf_l O hZF generic))) φ sign Z (j ω) (j a) x := by
  have hE := preserves_zf_l O hZF generic
  obtain ⟨j₀,checks,_,_⟩ := check_map_l O hZF generic hb
  have eq : j₀ = j := funext fun z => (gval_check_map_l O hZF generic hb j₀ checks z (j z)).mp (ground z)
  subst j₀
  have read s t (cs : Check_d M b ω s) (ct : Check_d M b a t) :
      (∃ p, G p ∧ Forces_d M Q T Q (dq_signed_m φ sign) (⟨fun i => [r,s,t,τ].get i,fun _ => r⟩ : Env M 4) p) ↔
        Dq_signed_d (kp_pair_l (ZF.modelsKP hE)) φ sign Z (j ω) (j a) x := by
    let ρ : Env M 4 := ⟨fun i => [r,s,t,τ].get i,fun _ => r⟩
    let η : Env E 4 := ⟨fun i => [Z,j ω,j a,x].get i,fun _ => Z⟩
    exact (forcing_closed_truth_l hZF O generic _ (dq_signed_closed_l hc sign) ρ η
      (Fin.cases value (Fin.cases (checks ω s cs) (Fin.cases (checks a t ct) (Fin.cases query (fun i => Fin.elim0 i)))))).trans
        (dq_signed_sat_l (kp_pair_l (ZF.modelsKP hE)) (ZF.modelsKP hE) hc sign η)
  constructor
  · rintro ⟨p,hp,s,t,cs,ct,force⟩
    exact (read s t cs ct).mp ⟨p,hp,force⟩
  · intro truth
    obtain ⟨s,cs,_,_⟩ := zf_check_l M hZF (generic.proper b hb).1 ω
    obtain ⟨t,ct,_,_⟩ := zf_check_l M hZF (generic.proper b hb).1 a
    obtain ⟨p,hp,force⟩ := (read s t cs ct).mpr truth
    exact ⟨p,hp,s,t,cs,ct,force⟩

/-- 同一最小坏代码对任意原查询产生一侧被原泛型接受的真实力迫条件。 -/
theorem qs_cover_l {φ : Formula 1 4} (hc : φ.FreeClosed) {r ω a τ b : M.Domain} (hb : G b)
    (j : M.Domain → (E).Domain) (ground : ∀ z, Gval_d M Q T Q G z (j z))
    {Z x c : (E).Domain} (value : Qval_d M Q T Q G r Z) (query : Qval_d M Q T Q G τ x)
    (hw : (E).IsOmega (j ω)) (binary : Descriptive.Bc_binary_d (j ω) (j a))
    (least : Dm_min_d (preserves_zf_l O hZF generic) φ Z (j a) c) (hx : (E).mem x Z) :
    (∃ p, G p ∧ Qs_force_d φ true Q T r ω a τ b p) ∨ ∃ p, G p ∧ Qs_force_d φ false Q T r ω a τ b p := by
  exact (least.signed_queries_l (preserves_zf_l O hZF generic) hc hw binary x hx).imp
    ((qs_truth_l hZF O generic hc true hb j ground value query).mpr)
    ((qs_truth_l hZF O generic hc false hb j ground value query).mpr)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 正负根检查读取原源模型的力迫关系

相对化将所有量词限制在固定源集合中，故该检查是背景的有界公式。
参数实数、规范实数并名字、查询名字和检查基准均保留原对象。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u

def qs_force0_m (φ : Formula 1 4) (sign : Bool) : Formula 1 8 :=
  qs_force_m φ sign (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)

theorem qs_force0_closed_l {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool) : (qs_force0_m φ sign).FreeClosed :=
  qs_force_closed_l hc sign _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl

def qs_check_m {n} (φ : Formula 1 4) (sign : Bool) (X Q T r ω a b τ p : Term n) : Formula 1 n :=
  lr_rel_m (qs_force0_m φ sign) X (fun i => [Q,T,r,ω,a,τ,b,p].get i)

theorem qs_check_delta_l {n} (φ : Formula 1 4) (sign : Bool) (X Q T r ω a b τ p : Term n) :
    (qs_check_m φ sign X Q T r ω a b τ p).IsDelta0 := lr_rel_delta_l ..

@[simp] theorem qs_check_closed_l {n} {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool) (X Q T r ω a b τ p : Term n)
    (hX : X.freeSupport = []) (hQ : Q.freeSupport = []) (hT : T.freeSupport = []) (hr : r.freeSupport = [])
    (hw : ω.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) (hτ : τ.freeSupport = []) (hp : p.freeSupport = []) :
    (qs_check_m φ sign X Q T r ω a b τ p).FreeClosed :=
  lr_rel_closed_l _ (qs_force0_closed_l hc sign) _ _ hX
    (Fin.cases hQ (Fin.cases hT (Fin.cases hr (Fin.cases hw (Fin.cases ha
      (Fin.cases hτ (Fin.cases hb (Fin.cases hp (fun i => Fin.elim0 i)))))))))

def Qs_check_d {M : Structure.{u}} (φ : Formula 1 4) (sign : Bool) (X Q T r ω a b τ p : M.Domain) : Prop :=
  Formula.satisfies (⟨fun i => [X,Q,T,r,ω,a,b,τ,p].get i,fun _ => X⟩ : Env M 9)
    (qs_check_m φ sign (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8))

theorem qs_check_sat_l {M : Structure.{u}} {n} {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool)
    (ρ : Env M n) (X Q T r ω a b τ p : Term n) :
    Formula.satisfies ρ (qs_check_m φ sign X Q T r ω a b τ p) ↔
      Qs_check_d φ sign (X.eval ρ) (Q.eval ρ) (T.eval ρ) (r.eval ρ) (ω.eval ρ) (a.eval ρ) (b.eval ρ) (τ.eval ρ) (p.eval ρ) :=
  lr_rel_arguments_l _ (qs_force0_closed_l hc sign) _ _ _ _ _ _ rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))))

theorem qs_check_read_l {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) {c X R : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (hN : Extensional (smdl_structure_l I (R := R) source.1.2.1))
    {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool)
    (Q T r ω a b τ p : (smdl_structure_l I (R := R) source.1.2.1).Domain) :
    Qs_check_d φ sign X Q.val T.val r.val ω.val a.val b.val τ.val p.val ↔ Qs_force_d φ sign Q T r ω a τ b p := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let ρ : Env N 8 := ⟨fun i => [Q,T,r,ω,a,τ,b,p].get i,fun _ => Q⟩
  exact (lr_rel_decode_l I source.1 source.2 trans _ (qs_force0_closed_l hc sign) ρ _ _ _ rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))))).trans
      (qs_force_sat_l hN hc sign ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一名字位置上的正负根检查及其有限可见性 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}}

def Qs_at_d (φ : Formula 1 4) (sign : Bool) (X Q T r ω a n e f v w : M.Domain) : Prop :=
  ∀ o i j p b τ, M.mem o n → M.mem i n → M.mem j n → (∀ y, ¬ M.mem y o) →
    Rd_entry_d o i v → Rd_entry_d o j w → Rd_entry_d i b e → Rd_entry_d j τ e → Rd_entry_d o p f →
      Qs_check_d φ sign X Q T r ω a b τ p

def qs_at_m {d} (φ : Formula 1 4) (sign : Bool) (X Q T r ω a n e f v w : Term d) : Formula 1 d :=
  set[d] ⟪∀ o i j p b τ, o ∈ ⌜n⌝ₛ → i ∈ ⌜n⌝ₛ → j ∈ ⌜n⌝ₛ → ⌜Formula.isEmpty⌝ₚ(o) →
    ⌜rd_entry0_m⌝ₚ(o,i,⌜v⌝ₛ) → ⌜rd_entry0_m⌝ₚ(o,j,⌜w⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(i,b,⌜e⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j,τ,⌜e⌝ₛ) → ⌜rd_entry0_m⌝ₚ(o,p,⌜f⌝ₛ) →
      ⌜qs_check_m φ sign⌝ₚ(⌜X⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,⌜r⌝ₛ,⌜ω⌝ₛ,⌜a⌝ₛ,b,τ,p)⟫

@[simp] theorem qs_at_closed_l {d} {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool) (X Q T r ω a n e f v w : Term d)
    (hX : X.freeSupport = []) (hQ : Q.freeSupport = []) (hT : T.freeSupport = []) (hr : r.freeSupport = [])
    (hw : ω.freeSupport = []) (ha : a.freeSupport = []) (hn : n.freeSupport = []) (he : e.freeSupport = [])
    (hf : f.freeSupport = []) (hv : v.freeSupport = []) (hx : w.freeSupport = []) :
    (qs_at_m φ sign X Q T r ω a n e f v w).FreeClosed := by
  simp -implicitDefEqProofs [qs_at_m,Definitional.Formula.FreeClosed,hX,hQ,hT,hr,hw,ha,hn,he,hf,hv,hx,hc]

theorem qs_at_sat_l (hE : Extensional M) {d} {φ : Formula 1 4} (hc : φ.FreeClosed) (sign : Bool)
    (ρ : Env M d) (X Q T r ω a n e f v w : Term d) :
    Formula.satisfies ρ (qs_at_m φ sign X Q T r ω a n e f v w) ↔
      Qs_at_d φ sign (X.eval ρ) (Q.eval ρ) (T.eval ρ) (r.eval ρ) (ω.eval ρ) (a.eval ρ)
        (n.eval ρ) (e.eval ρ) (f.eval ρ) (v.eval ρ) (w.eval ρ) := by
  simp only [qs_at_m,Qs_at_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_isEmpty_iff,rd_entry0_sat_l hE,qs_check_sat_l hc,Definitional.Term.eval_weaken]
  rfl

theorem Qs_at_d.prefix_l {φ : Formula 1 4} {sign : Bool} {X Q T r ω a n m e f v w e' f' v' w' : M.Domain}
    (h : Qs_at_d φ sign X Q T r ω a m e f v w) (sub : M.MemberSubset n m)
    (ee : M.MemberSubset e' e) (ff : M.MemberSubset f' f) (vv : M.MemberSubset v' v) (ww : M.MemberSubset w' w) :
    Qs_at_d φ sign X Q T r ω a n e' f' v' w' := by
  have move {A B i y : M.Domain} (sub : M.MemberSubset A B) (iy : Rd_entry_d i y A) : Rd_entry_d i y B :=
    iy.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  exact fun o i j p b τ ho hi hj empty oi oj ib jτ op => h o i j p b τ
    (sub o ho) (sub i hi) (sub j hj) empty (move vv oi) (move ww oj) (move ee ib) (move ee jτ) (move ff op)

/-- 根所需的三个位置具有同一内部自然数上界，故有限检查恢复整枝的根断言。 -/
theorem qs_branch_l (hZF : M.Models ZF) {φ : Formula 1 4} {sign : Bool} {X Q T r ω a e f v w : M.Domain}
    (hw : M.IsOmega ω)
    (prefixes : ∀ n, M.mem n ω → ∃ e' f' v' w', Qs_at_d φ sign X Q T r ω a n e' f' v' w' ∧
      M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) e' e n ∧ M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) f' f n ∧
      M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) v' v n ∧ M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) w' w n) :
    Qs_at_d φ sign X Q T r ω a ω e f v w := by
  intro o i j p b τ ho hi hj empty oi oj ib jτ op
  obtain ⟨k,hk,ok,ik⟩ := at_upper_l hZF hw ho hi
  obtain ⟨n,hn,kn,jn⟩ := at_upper_l hZF hw hk hj
  have nt := (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive
  have on := nt k kn o ok
  have hin := nt k kn i ik
  obtain ⟨_,_,_,_,check,ce,cf,cv,cw⟩ := prefixes n hn
  exact check o i j p b τ on hin jn empty ((cv.2 o i).mpr ⟨on,oi⟩) ((cw.2 o j).mpr ⟨on,oj⟩)
    ((ce.2 i b).mpr ⟨hin,ib⟩) ((ce.2 j τ).mpr ⟨jn,jτ⟩) ((cf.2 o p).mpr ⟨on,op⟩)

end YesMetaZFC.Model.Forcing.Internal
