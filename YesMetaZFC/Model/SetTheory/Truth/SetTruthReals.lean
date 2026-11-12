import YesMetaZFC.SetTheory.InnerModel.Separation.Formula
import YesMetaZFC.SetTheory.Collapse.Transport
import YesMetaZFC.Model.SetTheory.LevyReflection.Decode
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Internal.NaturalBasis
import YesMetaZFC.SetTheory.Collapse.FunctionSupport
import YesMetaZFC.Model.SetTheory.Internal.BinaryDecode

/-! # 集合结构的完整真值及原 Σ₁(ℝ) 见证

集合 Q 的成员结构可以不传递，也无需满足外延性。成员满单射在 Q 上限制为
真正的满同构，因而保持任意原公式；此处不把矩阵限制为 Δ₀。
Σ₁(ℝ) 按原 8.3 定义为存在 Q ⊇ ℝ，使 Q 满足给定公式，参数均为实数。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

def St_d {n} (Q : M.Domain) (φ : Formula 1 n) (x : Fin n → M.Domain) : Prop :=
  ∃ h : Nonempty {a // M.mem a Q}, ∃ ρ : Env (rt_model_l Q h) n,
    (∀ i, (ρ.bound i).val = x i) ∧ Formula.satisfies ρ φ

def Sr_truth_d {n} (B : M.Domain) (φ : Formula 1 n) (x : Fin n → M.Domain) : Prop :=
  (∀ i, M.mem (x i) B) ∧ ∃ Q, M.MemberSubset B Q ∧ St_d Q φ x

theorem st_image_l (e : M.Domain → N.Domain) (ei : Function.Injective e)
    (ef : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    {n} (Q : M.Domain) (φ : Formula 1 n) (hc : φ.FreeClosed) (x : Fin n → M.Domain) :
    St_d Q φ x ↔ St_d (e Q) φ (fun i => e (x i)) := by
  have mem a b : M.mem a b ↔ N.mem (e a) (e b) :=
    ⟨fun h => (ef b (e a)).mpr ⟨a,h,rfl⟩,
      fun h => (ef b (e a)).mp h |>.elim fun z hz => ei hz.2 ▸ hz.1⟩
  have transfer (h : Nonempty {a // M.mem a Q}) (k : Nonempty {a // N.mem a (e Q)})
      (ρ : Env (rt_model_l Q h) n) :
      Formula.satisfies ρ φ ↔ Formula.satisfies
        (image_env_l (M := rt_model_l Q h) (N := rt_model_l (e Q) k)
          (fun a => ⟨e a.val,(mem a.val Q).mp a.property⟩) ρ) φ := by
    apply formula_image_l
    · intro b
      obtain ⟨a,ha,eq⟩ := (ef Q b.val).mp b.property
      exact ⟨⟨a,ha⟩,Subtype.ext eq⟩
    · exact fun a b => mem a.val b.val
  constructor
  · rintro ⟨h,ρ,hx,truth⟩
    have k : Nonempty {a // N.mem a (e Q)} := h.elim fun a => ⟨⟨e a.val,(mem a.val Q).mp a.property⟩⟩
    exact ⟨k,_,fun i => congrArg e (hx i),(transfer h k ρ).mp truth⟩
  · rintro ⟨k,η,hx,truth⟩
    have h : Nonempty {a // M.mem a Q} := k.elim fun b =>
      ((ef Q b.val).mp b.property).elim fun a ha => ⟨⟨a,ha.1⟩⟩
    have inside i : M.mem (x i) Q := by
      have hi : N.mem (η.bound i).val (e Q) := (η.bound i).property
      rw [hx i] at hi
      exact (mem (x i) Q).mpr hi
    obtain ⟨a⟩ := (show Nonempty {a // M.mem a Q} from h)
    let ρ : Env (rt_model_l Q h) n := ⟨fun i => ⟨x i,inside i⟩,fun _ => a⟩
    refine ⟨h,ρ,fun _ => rfl,(transfer h k ρ).mpr ?_⟩
    exact (Formula.closed_env_l φ hc (funext fun i => Subtype.ext (hx i).symm)).mpr truth

/-- 见证及包含全部实数的条件一同向上运输；无需整个大模型初等。 -/
theorem Sr_truth_d.image_l (e : M.Domain → N.Domain) (ei : Function.Injective e)
    (ef : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    {n B} {φ : Formula 1 n} (hc : φ.FreeClosed) {x : Fin n → M.Domain}
    (truth : Sr_truth_d B φ x) : Sr_truth_d (e B) φ (fun i => e (x i)) := by
  obtain ⟨reals,Q,sub,sat⟩ := truth
  refine ⟨fun i => (ef B (e (x i))).mpr ⟨x i,reals i,rfl⟩,e Q,?_,
    (st_image_l e ei ef Q φ hc x).mp sat⟩
  intro y hy
  obtain ⟨a,ha,rfl⟩ := (ef B y).mp hy
  exact (ef Q (e a)).mpr ⟨a,sub a ha,rfl⟩

end YesMetaZFC.SetTheory.InnerModel

/-! ## 任意见证集合的原公式相对化

见证集合未必传递，所以连定义原子中的量词也必须限制到该集合。
以下编译逐公式保留真实成员结构的满足关系，并给出原 8.3 的一阶公式。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def st_rel_m : {n d : Nat} → Formula 1 n → Term d → (Fin n → Term d) → Formula 1 d
  | _, _, .falsum, _, _ => .falsum
  | _, _, .truth, _, _ => .truth
  | _, _, .mem s t, _, e => .mem (s.bind e) (t.bind e)
  | _, _, .atom .extensionalEq _ ts, Q, e => Formula.forallMem Q
      (.iff (.mem .newest ((ts.get 0).bind e).weaken) (.mem .newest ((ts.get 1).bind e).weaken))
  | _, _, .atom .subset _ ts, Q, e => Formula.forallMem Q
      (.imp (.mem .newest ((ts.get 0).bind e).weaken) (.mem .newest ((ts.get 1).bind e).weaken))
  | _, _, .neg φ, Q, e => .neg (st_rel_m φ Q e)
  | _, _, .conj φ ψ, Q, e => .conj (st_rel_m φ Q e) (st_rel_m ψ Q e)
  | _, _, .disj φ ψ, Q, e => .disj (st_rel_m φ Q e) (st_rel_m ψ Q e)
  | _, _, .imp φ ψ, Q, e => .imp (st_rel_m φ Q e) (st_rel_m ψ Q e)
  | _, _, .iff φ ψ, Q, e => .iff (st_rel_m φ Q e) (st_rel_m ψ Q e)
  | _, _, .existsE φ, Q, e => Formula.existsMem Q
      (st_rel_m φ Q.weaken (Fin.cases .newest (fun i => (e i).weaken)))
  | _, _, .forallE φ, Q, e => Formula.forallMem Q
      (st_rel_m φ Q.weaken (Fin.cases .newest (fun i => (e i).weaken)))

@[simp] theorem st_rel_closed_l {n d} (φ : Formula 1 n) (hc : φ.FreeClosed)
    (Q : Term d) (e : Fin n → Term d) (hq : Q.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) :
    (st_rel_m φ Q e).FreeClosed := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hc
  case falsum | truth => trivial
  case mem s t => exact ⟨(Definitional.Term.freeSupport_bind_of_closed e he s).trans hc.1,
    (Definitional.Term.freeSupport_bind_of_closed e he t).trans hc.2⟩
  case atom r hr ts =>
    have closed i := (Definitional.Term.freeSupport_bind_of_closed e he (ts.get i)).trans (hc i)
    cases r <;> simp only [st_rel_m, Formula.forallMem, Definitional.Formula.FreeClosed]
      <;> exact ⟨⟨rfl,by simpa using hq⟩,⟨⟨rfl,by simpa using closed 0⟩,⟨rfl,by simpa using closed 1⟩⟩⟩
  case neg φ ih => exact ih hc Q e hq he
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    exact ⟨ih hc.1 Q e hq he,jh hc.2 Q e hq he⟩
  case existsE φ ih | forallE φ ih =>
    exact ⟨⟨rfl,by simpa using hq⟩,ih hc Q.weaken _ (by simpa using hq)
      (Fin.cases rfl (fun i => by simpa using he i))⟩

theorem st_rel_delta_l {n d} (φ : Formula 1 n) (Q : Term d) (e : Fin n → Term d) :
    (st_rel_m φ Q e).IsDelta0 := by
  induction φ generalizing d with
  | falsum => exact .falsum
  | truth => exact .truth
  | mem s t => exact .mem _ _
  | atom r hr ts => cases r <;> first
    | exact .forallMem _ (.iff (.mem _ _) (.mem _ _))
    | exact .forallMem _ (.imp (.mem _ _) (.mem _ _))
  | neg φ ih => exact .neg (ih Q e)
  | conj φ ψ ih jh => exact .conj (ih Q e) (jh Q e)
  | disj φ ψ ih jh => exact .disj (ih Q e) (jh Q e)
  | imp φ ψ ih jh => exact .imp (ih Q e) (jh Q e)
  | iff φ ψ ih jh => exact .iff (ih Q e) (jh Q e)
  | existsE φ ih => exact .existsMem _ (ih _ _)
  | forallE φ ih => exact .forallMem _ (ih _ _)

theorem st_rel_sat_l {Q : M.Domain} (hn : Nonempty {a // M.mem a Q}) {n d}
    (φ : Formula 1 n) (hc : φ.FreeClosed) (η : Env (rt_model_l Q hn) n)
    (ρ : Env M d) (T : Term d) (e : Fin n → Term d) (ht : T.eval ρ = Q)
    (he : ∀ i, (e i).eval ρ = (η.bound i).val) :
    Formula.satisfies ρ (st_rel_m φ T e) ↔ Formula.satisfies η φ := by
  have term {n d} (η : Env (rt_model_l Q hn) n) (ρ : Env M d) (e : Fin n → Term d)
      (he : ∀ i, (e i).eval ρ = (η.bound i).val) (t : Term n) (hc : t.freeSupport = []) :
      (t.bind e).eval ρ = (t.eval η).val := by
    obtain ⟨i,rfl⟩ := rt_term_l t hc
    exact he i
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hc
  case falsum | truth => simp only [st_rel_m, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff]
  case mem s t => simp only [st_rel_m, Formula.satisfies_mem_iff, term η ρ e he s hc.1,term η ρ e he t hc.2]; rfl
  case atom r hr ts =>
    cases r <;> simp only [st_rel_m,Formula.satisfies_forallMem_iff,Formula.satisfies_iff_iff,
      Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken,
      Definitional.Term.eval_newest,ht,term η ρ e he (ts.get 0) (hc 0),term η ρ e he (ts.get 1) (hc 1),
      Formula.satisfies_atom_extensionalEq_iff,Formula.satisfies_atom_subset_iff]
      <;> exact ⟨fun h a => h a.val a.property,fun h a ha => h ⟨a,ha⟩⟩
  case neg φ ih => simpa only [st_rel_m,Formula.satisfies_neg_iff] using not_congr (ih hc η ρ T e ht he)
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [st_rel_m,Formula.satisfies_conj_iff,Formula.satisfies_disj_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff,ih hc.1 η ρ T e ht he,jh hc.2 η ρ T e ht he]
  case existsE φ ih | forallE φ ih =>
    have tr (a : (rt_model_l Q hn).Domain) := ih hc (η.push a) (ρ.push a.val) T.weaken
      (Fin.cases .newest (fun i => (e i).weaken)) (by simpa using ht)
      (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken ρ a.val (e i)).trans (he i)))
    first
    | simp only [st_rel_m,Formula.satisfies_existsMem_iff,Formula.satisfies_exists_iff,ht]
      exact ⟨fun ⟨a,ha,h⟩ => ⟨⟨a,ha⟩,(tr ⟨a,ha⟩).mp h⟩,fun ⟨a,h⟩ => ⟨a.val,a.property,(tr a).mpr h⟩⟩
    | simp only [st_rel_m,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,ht]
      exact ⟨fun h a => (tr a).mp (h a.val a.property),fun h a ha => (tr ⟨a,ha⟩).mpr (h ⟨a,ha⟩)⟩

def st_params_m : {n d : Nat} → Term d → (Fin n → Term d) → Formula 1 d
  | 0, _, _, _ => .truth
  | _+1, _, Q, x => .conj (.mem (x 0) Q) (st_params_m Q (fun i => x i.succ))

@[simp] theorem st_params_closed_l {n d} (Q : Term d) (x : Fin n → Term d)
    (hq : Q.freeSupport = []) (hx : ∀ i, (x i).freeSupport = []) : (st_params_m Q x).FreeClosed := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨⟨hx 0,hq⟩,ih _ (fun i => hx i.succ)⟩

theorem st_params_sat_l {n d} (ρ : Env M d) (Q : Term d) (x : Fin n → Term d) :
    Formula.satisfies ρ (st_params_m Q x) ↔ ∀ i, M.mem ((x i).eval ρ) (Q.eval ρ) := by
  induction n with
  | zero => exact ⟨fun _ i => Fin.elim0 i,fun _ => trivial⟩
  | succ n ih =>
    simp only [st_params_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,ih]
    exact ⟨fun h => Fin.cases h.1 h.2,fun h => ⟨h 0,fun i => h i.succ⟩⟩

def st_m {n d} (φ : Formula 1 n) (Q : Term d) (x : Fin n → Term d) : Formula 1 d :=
  .conj (Formula.existsMem Q .truth) (.conj (st_params_m Q x) (st_rel_m φ Q x))

@[simp] theorem st_closed_l {n d} (φ : Formula 1 n) (hc : φ.FreeClosed)
    (Q : Term d) (x : Fin n → Term d) (hq : Q.freeSupport = []) (hx : ∀ i, (x i).freeSupport = []) :
    (st_m φ Q x).FreeClosed := ⟨⟨⟨rfl,by simpa using hq⟩,trivial⟩,st_params_closed_l Q x hq hx,st_rel_closed_l φ hc Q x hq hx⟩

theorem st_sat_l {n d} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env M d) (Q : Term d) (x : Fin n → Term d) :
    Formula.satisfies ρ (st_m φ Q x) ↔ St_d (Q.eval ρ) φ (fun i => (x i).eval ρ) := by
  simp only [st_m,Formula.satisfies_conj_iff,Formula.satisfies_existsMem_iff,Formula.satisfies_truth_iff,st_params_sat_l]
  constructor
  · rintro ⟨⟨a,ha,_⟩,inside,h⟩
    let hn : Nonempty {a // M.mem a (Q.eval ρ)} := ⟨⟨a,ha⟩⟩
    let η : Env (rt_model_l (Q.eval ρ) hn) n := ⟨fun i => ⟨(x i).eval ρ,inside i⟩,fun _ => ⟨a,ha⟩⟩
    exact ⟨hn,η,fun _ => rfl,(st_rel_sat_l hn φ hc η ρ Q x rfl (fun _ => rfl)).mp h⟩
  · rintro ⟨hn,η,hx,h⟩
    obtain ⟨a⟩ := (show Nonempty {a // M.mem a (Q.eval ρ)} from hn)
    refine ⟨⟨a.val,a.property,trivial⟩,fun i => ?_,(st_rel_sat_l hn φ hc η ρ Q x rfl (fun i => (hx i).symm)).mpr h⟩
    have hi : M.mem (η.bound i).val (Q.eval ρ) := (η.bound i).property
    rw [hx i] at hi
    exact hi

end YesMetaZFC.SetTheory.InnerModel

/-! ## 有限成员同余条件下的见证规范化

原存在见证允许非传递、非外延的成员结构。把一条成员同余句子放入矩阵，
便能在 KPi 背景中实际构造传递坍塌并运输整个原公式。参数随图运输，
本模块不将“参数被固定”或“值域含全部实数”混入坍塌结论。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

/-- 传递见证自动满足有限同余条件，不必附加源模型理论。 -/
theorem st_congr_l (hE : Extensional M) {Q : M.Domain} (ht : M.TransitiveSet Q)
    {n} {φ : Formula 1 n} {x : Fin n → M.Domain} :
    St_d Q (.conj mc_congr_m φ) x ↔ St_d Q φ x := by
  constructor
  · rintro ⟨hn,ρ,hx,hs⟩
    exact ⟨hn,ρ,hx,(Formula.satisfies_conj_iff ..).mp hs |>.2⟩
  · rintro ⟨hn,ρ,hx,hs⟩
    refine ⟨hn,ρ,hx,(Formula.satisfies_conj_iff ..).mpr ⟨(mc_congr_sat_l ρ).mpr ?_,hs⟩⟩
    intro a b eq z
    exact (mc_transitive_ext_l hE ht).congr_l a.val a.property b.val b.property
      (fun t ht => eq ⟨t,ht⟩) z.val z.property

/-- 满成员映射直接运输实际有限参数和整条公式；不选择全域代表元函数。 -/
theorem st_map_l {Q B F : M.Domain} (hf : Mc_map_d Q B F)
    {n} {φ : Formula 1 n} (hc : φ.FreeClosed) {x : Fin n → M.Domain} (hs : St_d Q φ x) :
    ∃ y, (∀ i, Rd_entry_d (x i) (y i) F) ∧ St_d B φ y := by
  obtain ⟨hn,ρ,hx,sat⟩ := hs
  have hb := hf.nonempty_l hn
  have liftParams {k} (a : Fin k → (rt_model_l Q hn).Domain) :
      ∃ b : Fin k → (rt_model_l B hb).Domain, ∀ i, Rd_entry_d (a i).val (b i).val F := by
    induction k with
    | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i⟩
    | succ k ih =>
      obtain ⟨b,he⟩ := ih (fun i => a i.succ)
      obtain ⟨z,hz,edge⟩ := hf.function.2.1 (a 0).val (a 0).property
      exact ⟨Fin.cases ⟨z,hz⟩ b,Fin.cases edge he⟩
  obtain ⟨y,he⟩ := liftParams ρ.bound
  have ne := hb
  obtain ⟨z⟩ := ne
  let η : Env (rt_model_l B hb) n := ⟨y,fun _ => z⟩
  exact ⟨fun i => (y i).val,fun i => hx i ▸ he i,
    hb,η,fun _ => rfl,(hf.formula_l hn hb φ hc ρ η he).mp sat⟩

/-- 实际构造传递见证、坍塌图及参数像，不假设见证满足任何集合论。 -/
theorem st_collapse_l (hM : M.Models KPi) {Q : M.Domain} {n} {φ : Formula 1 n}
    (hc : φ.FreeClosed) {x : Fin n → M.Domain} (hs : St_d Q (.conj mc_congr_m φ) x) :
    ∃ B F y, M.TransitiveSet B ∧ Mc_map_d Q B F ∧
      (∀ i, Rd_entry_d (x i) (y i) F) ∧ St_d B φ y ∧
      ∀ a b, Rd_entry_d a b F ↔ M.mem a Q ∧ Mc_value_d Q a b := by
  obtain ⟨hn,ρ,hx,sat⟩ := hs
  obtain ⟨congr,sat⟩ := (Formula.satisfies_conj_iff ..).mp sat
  have native := (mc_congr_sat_l ρ).mp congr
  have rel : Mc_congr_d Q := fun a ha b hb eq z hz =>
    native ⟨a,ha⟩ ⟨b,hb⟩ (fun t => eq t.val t.property) ⟨z,hz⟩
  obtain ⟨B,F,ht,hf,entry⟩ := mc_quotient_l hM rel
  obtain ⟨y,edge,truth⟩ := st_map_l hf hc ⟨hn,ρ,hx,sat⟩
  exact ⟨B,F,y,ht,hf,edge,truth,entry⟩

end YesMetaZFC.SetTheory.InnerModel

/-! ## 传递集合与有限反射的实际结构真值

有界公式在传递集合中绝对。任意原公式则用原隶属关系构造集合模型，
再与同一载体的成员结构识别；有限子公式闭性直接给出 St_d。
两者均不附加该集合满足 ZF 的条件。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}}

/-- 有界原公式在传递见证集合中绝对；不要求见证集合满足任何理论。 -/
theorem st_delta_l {Q : M.Domain} (trans : M.TransitiveSet Q) (ne : ∃ x, M.mem x Q)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (hd : φ.IsDelta0) (ρ : Env M n)
    (inside : ∀ i, M.mem (ρ.bound i) Q) : St_d Q φ ρ.bound ↔ Formula.satisfies ρ φ := by
  constructor
  · rintro ⟨hn,η,values,sat⟩
    exact (Formula.closed_env_l φ hc (funext values)).mp ((rt_model_delta_l trans hn hd η).mp sat)
  · intro sat
    obtain ⟨z,hz⟩ := ne
    let hn : Nonempty {x // M.mem x Q} := ⟨⟨z,hz⟩⟩
    let η : Env (rt_model_l Q hn) n := ⟨fun i => ⟨ρ.bound i,inside i⟩,fun _ => ⟨z,hz⟩⟩
    have keep : Formula.satisfies (image_env_l (M := rt_model_l Q hn) (N := M) Subtype.val η) φ ↔
        Formula.satisfies ρ φ := Formula.closed_env_l φ hc rfl
    exact ⟨hn,η,fun _ => rfl,(rt_model_delta_l trans hn hd η).mpr (keep.mpr sat)⟩

theorem st_reflect_l (hZF : M.Models ZF) {Q : M.Domain} (trans : M.TransitiveSet Q)
    (ne : ∃ x, M.mem x Q) {n} (φ : Formula 1 n) (hc : φ.FreeClosed)
    (closed : Lr_step_d (lr_queries_l φ hc) Q Q) (ρ : Env M n)
    (inside : ∀ i, M.mem (ρ.bound i) Q) :
    Formula.satisfies ρ φ ↔ St_d Q φ ρ.bound := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c,R,model,relation⟩ := smdl_membership_l I hZF ne
  let N := smdl_structure_l I (R := R) model.2.1
  obtain ⟨z,hz⟩ := ne
  let η : Env N n := ⟨fun i => ⟨ρ.bound i,inside i⟩,fun _ => ⟨z,hz⟩⟩
  have reflected : Lr_reflect_d φ Q := fun δ hd =>
    lr_reflect_core_l φ hc closed δ (δ.push Q) .newest (fun i => .bound i.succ) rfl (fun _ => rfl) hd
  have source := SetTheory.lr_model_l I model relation trans φ hc reflected ρ η (fun _ => rfl)
  let hn : Nonempty {x // M.mem x Q} := ⟨⟨z,hz⟩⟩
  let K := rt_model_l Q hn
  let e : N.Domain → K.Domain := fun x => ⟨x.val,x.property⟩
  have move := formula_image_l (M := N) (N := K) e
    (fun x => ⟨⟨x.val,x.property⟩,rfl⟩)
    (fun x y => smem_member_l I model relation x y) φ η
  refine source.trans ⟨fun h => ⟨hn,image_env_l e η,fun _ => rfl,move.mp h⟩,?_⟩
  rintro ⟨hn',δ,values,sat⟩
  apply move.mpr
  exact (Formula.closed_env_l φ hc (funext fun i => Subtype.ext (values i))).mp sat

end YesMetaZFC.SetTheory.InnerModel

/-! ## 任意集合见证中的自然数基集识别

用三条有限结构条件：成员同余、指定对象为序数、指定对象为最小归纳集。
传递源中这三条条件自动成立；一般源经实际坍塌后，其指定对象恰为背景 ω。
整个论证不要求源或传递值域满足 KP。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}}

/-- 指定槽保存自然数基集，其余槽及原矩阵保持原有顺序。 -/
def st_nat_m {n} (i : Fin n) (φ : Formula 1 n) : Formula 1 n :=
  .conj mc_congr_m (.conj (Formula.isOrdinal (.bound i)) (.conj (Formula.isOmega (.bound i)) φ))

theorem st_nat_closed_l {n} (i : Fin n) {φ : Formula 1 n} (hc : φ.FreeClosed) : (st_nat_m i φ).FreeClosed := by
  simp only [st_nat_m,Definitional.Formula.FreeClosed]
  exact ⟨mc_congr_closed_l,Formula.isOrdinal_freeClosed _ rfl,Formula.isOmega_freeClosed _ rfl,hc⟩

/-- 已构造的传递见证无需扩充源理论，即可生产这三条有限结构条件。 -/
theorem st_nat_transitive_l (hKP : M.Models KP) {Q : M.Domain} (ht : M.TransitiveSet Q)
    {n} {i : Fin n} {φ : Formula 1 n} {x : Fin n → M.Domain} (hω : M.IsOmega (x i)) :
    St_d Q (st_nat_m i φ) x ↔ St_d Q φ x := by
  rw [st_nat_m,st_congr_l hKP.1 ht]
  constructor
  · rintro ⟨hn,ρ,hx,hs⟩
    exact ⟨hn,ρ,hx,(Formula.satisfies_conj_iff ..).mp
      ((Formula.satisfies_conj_iff ..).mp hs).2 |>.2⟩
  · rintro ⟨hn,ρ,hx,hs⟩
    have hw : M.IsOmega (ρ.bound i).val := (hx i).symm ▸ hω
    exact ⟨hn,ρ,hx,(Formula.satisfies_conj_iff ..).mpr
      ⟨(Formula.satisfies_isOrdinal_iff ..).mpr (rt_ordinal_l ht hn _ (hw.isOrdinal hKP)),
        (Formula.satisfies_conj_iff ..).mpr
          ⟨(Formula.satisfies_isOmega_iff ..).mpr (rt_omega_l ht hn hKP.1 _ hw),hs⟩⟩⟩

/-- 非传递见证规范化后，原矩阵得到保留且指定槽自动等于背景 ω。 -/
theorem st_nat_collapse_l (hM : M.Models KPi) {ω Q : M.Domain} (hω : M.IsOmega ω)
    {n} {i : Fin n} {φ : Formula 1 n} (hc : φ.FreeClosed) {x : Fin n → M.Domain}
    (hs : St_d Q (st_nat_m i φ) x) :
    ∃ B F y, M.TransitiveSet B ∧ Mc_map_d Q B F ∧ y i = ω ∧
      (∀ i, Rd_entry_d (x i) (y i) F) ∧ St_d B φ y ∧
      ∀ a b, Rd_entry_d a b F ↔ M.mem a Q ∧ Mc_value_d Q a b := by
  have closed : ((.conj (Formula.isOrdinal (.bound i))
      (.conj (Formula.isOmega (.bound i)) φ)) : Formula 1 n).FreeClosed :=
    ⟨Formula.isOrdinal_freeClosed _ rfl,Formula.isOmega_freeClosed _ rfl,hc⟩
  obtain ⟨B,F,y,ht,hf,edge,truth,entry⟩ := st_collapse_l hM closed hs
  obtain ⟨hn,ρ,values,sat⟩ := truth
  obtain ⟨ordinal,sat⟩ := (Formula.satisfies_conj_iff ..).mp sat
  obtain ⟨natural,sat⟩ := (Formula.satisfies_conj_iff ..).mp sat
  have eq := rt_omega_eq_l ht hn (KPi.models_iff_l.mp hM).1 hω (ρ.bound i)
    ((Formula.satisfies_isOrdinal_iff ..).mp ordinal) ((Formula.satisfies_isOmega_iff ..).mp natural)
  exact ⟨B,F,y,ht,hf,(values i).symm.trans eq,edge,⟨hn,ρ,values,sat⟩,entry⟩

end YesMetaZFC.SetTheory.InnerModel

/-! ## 特殊实数见证与完整自然数支撑

同一有限公式同时记录原矩阵、自然数识别及常零、后继图。任意成员见证
经满坍塌后，图的原生解释转成背景中的实际边，遂由内部归纳恢复源中
全部自然数；两个特殊实数参数也由其图方程固定。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}}

def st_basis_m {n} (w z c s : Fin n) (φ : Formula 1 n) : Formula 1 n :=
  st_nat_m w (.conj (mc_nat_m (.bound w) (.bound z) (.bound c) (.bound s)) φ)

theorem st_basis_closed_l {n} (w z c s : Fin n) {φ : Formula 1 n} (hc : φ.FreeClosed) :
    (st_basis_m w z c s φ).FreeClosed :=
  st_nat_closed_l w ⟨mc_nat_m_freeClosed _ _ _ _ rfl rfl rfl rfl,hc⟩

theorem st_basis_transitive_l (hKP : M.Models KP) {Q : M.Domain} (ht : M.TransitiveSet Q)
    {n} {w z c s : Fin n} {φ : Formula 1 n} {x : Fin n → M.Domain}
    (h : Mc_nat_d (x w) (x z) (x c) (x s)) :
    St_d Q (st_basis_m w z c s φ) x ↔ St_d Q φ x := by
  rw [st_basis_m,st_nat_transitive_l hKP ht h.omega]
  constructor
  · rintro ⟨hn,ρ,hx,hs⟩
    exact ⟨hn,ρ,hx,((Formula.satisfies_conj_iff ..).mp hs).2⟩
  · rintro ⟨hn,ρ,hx,hs⟩
    have basis : Mc_nat_d (ρ.bound w).val (ρ.bound z).val (ρ.bound c).val (ρ.bound s).val := by
      simpa only [hx] using h
    exact ⟨hn,ρ,hx,(Formula.satisfies_conj_iff ..).mpr
      ⟨(mc_nat_sat_l (rt_model_ext_l hKP.1 ht hn) ρ _ _ _ _).mpr
        (rt_nat_into_l ht hn hKP.1 _ _ _ _ basis),hs⟩⟩

/-- 两张指定的真实实数图由背景构造给出；任意见证只需满足同一有限公式。
源中全部自然数及其逐点固定性均为输出，不预先假设源传递或源模型理论。 -/
theorem st_basis_collapse_l (hM : M.Models KPi) {ω z₀ Q : M.Domain} {n}
    {w z c s : Fin n} {φ : Formula 1 n} (hc : φ.FreeClosed) {x : Fin n → M.Domain}
    (basis : Mc_nat_d ω z₀ (x c) (x s)) (hs : St_d Q (st_basis_m w z c s φ) x) :
    ∃ B F y, M.TransitiveSet B ∧ Mc_map_d Q B F ∧ y w = ω ∧ y z = z₀ ∧
      y c = x c ∧ y s = x s ∧ M.MemberSubset ω Q ∧
      (∀ a, M.mem a ω → Rd_entry_d a a F) ∧
      (∀ r v, Fn0_d ω ω r → (∀ a b, Rd_entry_d a b r → b = z₀ ∨ M.SuccessorOf b a) → Rd_entry_d r v F → r = v) ∧
      (∀ i, Rd_entry_d (x i) (y i) F) ∧
      St_d B φ y ∧ ∀ a b, Rd_entry_d a b F ↔ M.mem a Q ∧ Mc_value_d Q a b := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have closed : ((.conj (mc_nat_m (.bound w) (.bound z) (.bound c) (.bound s)) φ) : Formula 1 n).FreeClosed :=
    ⟨mc_nat_m_freeClosed _ _ _ _ rfl rfl rfl rfl,hc⟩
  obtain ⟨B,F,y,ht,hf,ew,edge,truth,entry⟩ := st_nat_collapse_l hM basis.omega closed hs
  obtain ⟨hn,ρ,values,sat⟩ := truth
  obtain ⟨native,sat⟩ := (Formula.satisfies_conj_iff ..).mp sat
  have native := (mc_nat_sat_l (rt_model_ext_l hKP.1 ht hn) ρ (.bound w) (.bound z) (.bound c) (.bound s)).mp native
  have hw : M.IsOmega (ρ.bound w).val := ((values w).trans ew).symm ▸ basis.omega
  have raw := rt_nat_out_l ht hn hKP.1 (ρ.bound w) (ρ.bound z) (ρ.bound c) (ρ.bound s) hw native
  have ez : y z = z₀ := (values z).symm.trans
    (hKP.1.eq_of_same_members _ _ (fun a => iff_of_false (raw.empty a) (basis.empty a)))
  have target : Mc_nat_d ω z₀ (y c) (y s) := by simpa only [values,ew,ez] using raw
  have ec : x c = y c := basis.constant.ext_l hKP.1 target.constant
    (fun a ha => ⟨z₀,(basis.constant_entry a z₀).mpr ⟨ha,rfl⟩,(target.constant_entry a z₀).mpr ⟨ha,rfl⟩⟩)
  have es : x s = y s := basis.successor.ext_l hKP.1 target.successor (fun a ha => by
    obtain ⟨b,hb,_⟩ := basis.omega.1.2 a ha
    exact ⟨b,(basis.successor_entry a b).mpr ⟨ha,hb⟩,(target.successor_entry a b).mpr ⟨ha,hb⟩⟩)
  obtain ⟨cover,fixed⟩ := hf.naturals_l hKP ht basis (edge c) (edge s)
    (fun a ha => (target.constant_entry a z₀).mpr ⟨ha,rfl⟩)
    (fun a ha b hb => (target.successor_entry a b).mpr ⟨ha,hb⟩)
  have binary r v (fr : Fn0_d ω ω r) (bits : ∀ a b, Rd_entry_d a b r → b = z₀ ∨ M.SuccessorOf b a)
      (er : Rd_entry_d r v F) : r = v :=
    hf.binary_fixed_l ht hKP.1 basis (ec.symm ▸ edge c) (es.symm ▸ edge s) fixed fr bits er
  exact ⟨B,F,y,ht,hf,ew,ez,ec.symm,es.symm,cover,fixed,binary,edge,⟨hn,ρ,values,sat⟩,entry⟩

end YesMetaZFC.SetTheory.InnerModel

/-! ## 有限解码闭包恢复完整背景实数

源只需包含背景实数，并满足原矩阵中的有限结构条件。任意背景实数先作
规范二值编码，编码在坍塌中固定；目标内的有界解码再由唯一性恢复原实数。
源、目标均不承担完整集合论，规范配对图也由实际 Δ₀ 证书识别。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal Descriptive
universe u
variable {M : Structure.{u}}

/-- 用原有界函数图定义源中的实数族，不依赖源的配对构造实例。 -/
def sr_space_m {d} (ω B : Term d) : Formula 1 d :=
  .forallE (.iff (.mem .newest B.weaken) (fn0_m ω.weaken ω.weaken .newest))
derive_free_closed sr_space_m

theorem sr_space_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B : Term d) :
    Formula.satisfies ρ (sr_space_m ω B) ↔ ∀ r, M.mem r (B.eval ρ) ↔ Fn0_d (ω.eval ρ) (ω.eval ρ) r := by
  simp only [sr_space_m,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,fn0_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

/-- 完整实数覆盖使源内函数空间断言精确恢复背景函数空间。 -/
theorem rt_reals_iff_l {Q : M.Domain} (ht : M.TransitiveSet Q) (hn : Nonempty {x // M.mem x Q})
    (hE : Extensional M) (w B : (rt_model_l Q hn).Domain)
    (cover : ∀ r, Fn0_d w.val w.val r → M.mem r Q) :
    (∀ r, (rt_model_l Q hn).mem r B ↔ Fn0_d w w r) ↔
      ∀ r, M.mem r B.val ↔ Fn0_d w.val w.val r := by
  constructor
  · intro h r
    constructor
    · intro hr
      let t : (rt_model_l Q hn).Domain := ⟨r,ht B.val B.property r hr⟩
      exact (rt_fn_l ht hn hE w w t).mp ((h t).mp hr)
    · intro fr
      let t : (rt_model_l Q hn).Domain := ⟨r,cover r fr⟩
      exact (h t).mpr ((rt_fn_l ht hn hE w w t).mpr fr)
  · exact fun h r => (h r.val).trans (rt_fn_l ht hn hE w w r).symm

theorem bc_reals_covered_l (hZF : M.Models ZF) {Q U g η z c s : M.Domain}
    (hg : Mc_map_d Q U g) (ht : M.TransitiveSet U) (hn : Nonempty {a // M.mem a U})
    (w X E : (rt_model_l U hn).Domain) (basis : Mc_nat_d w.val z c s)
    (ec : Rd_entry_d c c g) (es : Rd_entry_d s s g)
    (fixed : ∀ n, M.mem n w.val → Rd_entry_d n n g)
    (cover : ∀ r, Fn0_d w.val w.val r → M.mem r Q)
    (square : Oc_square_d w.val X.val η E.val) (closed : Bc_closed_d w X E) :
    ∀ r, Fn0_d w.val w.val r → M.mem r U := by
  intro r fr
  obtain ⟨b,binary,read⟩ := bc_encode_l hZF basis.omega fr
  obtain ⟨v,hv,edge⟩ := hg.function.2.1 b (cover b binary.1)
  have eq := hg.binary_fixed_l ht hZF.1 basis ec es fixed binary.1
    (fun n y ny => (binary.2 n y ny).imp_left (fun hy =>
      hZF.1.eq_of_same_members y z (fun t => iff_of_false (hy t) (basis.empty t)))) edge
  subst v
  let a : (rt_model_l U hn).Domain := ⟨b,hv⟩
  have graph := (bc_graph_read_l hZF square).mpr read
  obtain ⟨t,decoded⟩ := closed a ((rt_fn_l ht hn hZF.1 w w a).mpr binary.1)
    ((rt_bc_valid_l ht hn hZF.1 w X E a).mpr graph.valid_l)
  have exactGraph := (rt_bc_graph_l ht hn hZF.1 w X E a t).mp decoded
  exact (graph.unique_l hZF.1 exactGraph).symm ▸ t.property

def st_reals_m {n} (w z c s X a E : Fin n) (φ : Formula 1 n) : Formula 1 n :=
  st_basis_m w z c s (.conj (oc_square_m (.bound w) (.bound X) (.bound a) (.bound E))
    (.conj (bc_closed_m (.bound w) (.bound X) (.bound E)) φ))

theorem st_reals_closed_l {n} (w z c s X a E : Fin n) {φ : Formula 1 n} (hc : φ.FreeClosed) :
    (st_reals_m w z c s X a E φ).FreeClosed :=
  st_basis_closed_l w z c s ⟨oc_square_m_freeClosed _ _ _ _ rfl rfl rfl rfl,
    bc_closed_m_freeClosed _ _ _ rfl rfl rfl,hc⟩

/-- 已构造的传递见证可直接读出其中的实际自然数编号图。 -/
theorem st_reals_square_l (hKP : M.Models KP) {Q : M.Domain} (ht : M.TransitiveSet Q)
    {n} {w z c s X a E : Fin n} {φ : Formula 1 n} {x : Fin n → M.Domain}
    (hs : St_d Q (st_reals_m w z c s X a E φ) x) : Oc_square_d (x w) (x X) (x a) (x E) := by
  obtain ⟨hn,ρ,values,sat⟩ := hs
  simp only [st_reals_m,st_basis_m,st_nat_m,Formula.satisfies_conj_iff] at sat
  have square := (oc_square_sat_l hKP _ _ _ _ _).mp
    ((rt_model_delta_l ht hn (oc_square_delta_l ..) ρ).mp sat.2.2.2.2.1)
  change Oc_square_d (ρ.bound w).val (ρ.bound X).val (ρ.bound a).val (ρ.bound E).val at square
  simpa only [values] using square

/-- 原传递见证由背景实数覆盖自动产生有限解码闭包。 -/
theorem st_reals_transitive_l (hKP : M.Models KP) {Q : M.Domain} (ht : M.TransitiveSet Q)
    {n} {w z c s X a E : Fin n} {φ : Formula 1 n} {x : Fin n → M.Domain}
    (basis : Mc_nat_d (x w) (x z) (x c) (x s)) (square : Oc_square_d (x w) (x X) (x a) (x E))
    (cover : ∀ r, Fn0_d (x w) (x w) r → M.mem r Q) :
    St_d Q (st_reals_m w z c s X a E φ) x ↔ St_d Q φ x := by
  rw [st_reals_m,st_basis_transitive_l hKP ht basis]
  constructor
  · rintro ⟨hn,ρ,hx,hs⟩
    exact ⟨hn,ρ,hx,((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp hs).2).2⟩
  · rintro ⟨hn,ρ,hx,hs⟩
    have raw : Formula.satisfies (image_env_l (M := rt_model_l Q hn) (N := M) Subtype.val ρ)
        (oc_square_m (.bound w) (.bound X) (.bound a) (.bound E)) :=
      (oc_square_sat_l hKP _ _ _ _ _).mpr (by
        change Oc_square_d (ρ.bound w).val (ρ.bound X).val (ρ.bound a).val (ρ.bound E).val
        simpa only [hx] using square)
    have sq := (rt_model_delta_l ht hn (oc_square_delta_l ..) ρ).mpr raw
    have closure := rt_bc_closed_l ht hn hKP (ρ.bound w) (ρ.bound X) (ρ.bound E)
      (fun r fr => cover r (by simpa only [hx] using fr))
    exact ⟨hn,ρ,hx,(Formula.satisfies_conj_iff ..).mpr ⟨sq,(Formula.satisfies_conj_iff ..).mpr
      ⟨(bc_closed_sat_l (rt_model_ext_l hKP.1 ht hn) ρ _ _ _).mpr closure,hs⟩⟩⟩

/-- 原源的实数覆盖随有限见证规范化为目标的完整背景实数覆盖。 -/
theorem st_reals_collapse_l (hZF : M.Models ZF) {ω z₀ Q : M.Domain} {n}
    {w z c s X a E : Fin n} {φ : Formula 1 n} (hc : φ.FreeClosed) {x : Fin n → M.Domain}
    (basis : Mc_nat_d ω z₀ (x c) (x s)) (cover : ∀ r, Fn0_d ω ω r → M.mem r Q)
    (hs : St_d Q (st_reals_m w z c s X a E φ) x) :
    ∃ U g y, M.TransitiveSet U ∧ Mc_map_d Q U g ∧ y w = ω ∧ y z = z₀ ∧
      y c = x c ∧ y s = x s ∧ Oc_square_d ω (y X) (y a) (y E) ∧
      (∀ r, Fn0_d ω ω r → M.mem r U) ∧
      (∀ r v, Bc_binary_d ω r → Rd_entry_d r v g → r = v) ∧
      (∀ i, Rd_entry_d (x i) (y i) g) ∧ St_d U φ y ∧
      ∀ p q, Rd_entry_d p q g ↔ M.mem p Q ∧ Mc_value_d Q p q := by
  let hKP := ZF.modelsKP hZF
  have closed : ((.conj (oc_square_m (.bound w) (.bound X) (.bound a) (.bound E))
      (.conj (bc_closed_m (.bound w) (.bound X) (.bound E)) φ)) : Formula 1 n).FreeClosed :=
    ⟨oc_square_m_freeClosed _ _ _ _ rfl rfl rfl rfl,bc_closed_m_freeClosed _ _ _ rfl rfl rfl,hc⟩
  obtain ⟨U,g,y,ht,hg,ew,ez,ec,es,_,fixed,binary,edges,truth,entry⟩ := st_basis_collapse_l (ZF.models_kpi_l hZF) closed basis hs
  obtain ⟨hn,ρ,values,sat⟩ := truth
  obtain ⟨square,sat⟩ := (Formula.satisfies_conj_iff ..).mp sat
  obtain ⟨closure,sat⟩ := (Formula.satisfies_conj_iff ..).mp sat
  have square := (oc_square_sat_l hKP _ _ _ _ _).mp
    ((rt_model_delta_l ht hn (oc_square_delta_l ..) ρ).mp square)
  have closure := (bc_closed_sat_l (rt_model_ext_l hKP.1 ht hn) ρ (.bound w) (.bound X) (.bound E)).mp closure
  have basis' : Mc_nat_d (ρ.bound w).val z₀ (x c) (x s) := ((values w).trans ew).symm ▸ basis
  have all := bc_reals_covered_l hZF hg ht hn (ρ.bound w) (ρ.bound X) (ρ.bound E) basis'
    (ec ▸ edges c) (es ▸ edges s)
    (fun i hi => fixed i (by simpa only [values,ew] using hi))
    (fun r fr => cover r (by simpa only [values,ew] using fr)) square closure
  have fixed_binary r v (hr : Bc_binary_d ω r) (er : Rd_entry_d r v g) : r = v :=
    binary r v hr.1 (fun i j ij => (hr.2 i j ij).imp_left (fun empty =>
      hZF.1.eq_of_same_members j z₀ (fun t => iff_of_false (empty t) (basis.empty t)))) er
  have numbers : Oc_square_d ω (y X) (y a) (y E) := by
    change Oc_square_d (ρ.bound w).val (ρ.bound X).val (ρ.bound a).val (ρ.bound E).val at square
    simpa only [values,ew] using square
  refine ⟨U,g,y,ht,hg,ew,ez,ec,es,numbers,?_,fixed_binary,edges,⟨hn,ρ,values,sat⟩,entry⟩
  intro r fr
  exact all r (by simpa only [values,ew] using fr)

end YesMetaZFC.SetTheory.InnerModel
