import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.SetTheory.KP.Kuratowski
import YesMetaZFC.SetTheory.KP.Natural
import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Types.Embedding

/-! # 类型坐标的固定标签角色

第 i+1 个坐标必须是以内部自然数 i 为首坐标的 Kuratowski 对。
零标签与相邻标签的后继关系都是有界公式，因而在传递秩层间绝对。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Tr_tag_d (i p : M.Domain) : Prop := ∃ x, KPair_d M p i x

def tr_tag_m {d} (i p : Term d) : Formula 1 d := set[d] ⟪
  ∃ a ∈ ⌜p⌝ₛ, ∃ x ∈ a, ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜i⌝ₛ, x)⟫
derive_free_closed tr_tag_m

theorem tr_tag_delta_l {d} (i p : Term d) : (tr_tag_m i p).IsDelta0 :=
  .existsMem _ (.existsMem _ (kpair0_delta_l ..))

theorem tr_tag_sat_l (hE : Extensional M) {d} (ρ : Env M d) (i p : Term d) :
    Formula.satisfies ρ (tr_tag_m i p) ↔ Tr_tag_d (i.eval ρ) (p.eval ρ) := by
  simp only [tr_tag_m, Formula.satisfies_existsMem_iff, kpair0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨_, _, x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => by
    obtain ⟨a, ha, hx⟩ := (kpair_union_l M h x).mpr (Or.inr rfl)
    exact ⟨a, ha, x, hx, h⟩⟩

theorem Tr_tag_d.unique_l {i j p : M.Domain} (h : Tr_tag_d i p) (g : Tr_tag_d j p) : i = j := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := g
  exact (kpair_injective_l M hx hy).1

def Tr_zero_d (p : M.Domain) : Prop := ∃ i, (∀ x, ¬ M.mem x i) ∧ Tr_tag_d i p
def Tr_step_d (p q : M.Domain) : Prop := ∃ i j, Tr_tag_d i p ∧ Tr_tag_d j q ∧ M.SuccessorOf j i

def tr_zero_m {d} (p : Term d) : Formula 1 d := set[d] ⟪
  ∃ a ∈ ⌜p⌝ₛ, ∃ i ∈ a, (∀ x ∈ i, ⊥) ∧ ⌜tr_tag_m⌝ₚ(i, ⌜p⌝ₛ)⟫
derive_free_closed tr_zero_m

def tr_step_m {d} (p q : Term d) : Formula 1 d := set[d] ⟪
  ∃ a ∈ ⌜p⌝ₛ, ∃ i ∈ a, ∃ b ∈ ⌜q⌝ₛ, ∃ j ∈ b,
    ⌜tr_tag_m⌝ₚ(i, ⌜p⌝ₛ) ∧ ⌜tr_tag_m⌝ₚ(j, ⌜q⌝ₛ) ∧ ⌜KP.succ0_m⌝ₚ(j, i)⟫
derive_free_closed tr_step_m

theorem tr_zero_delta_l {d} (p : Term d) : (tr_zero_m p).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (.forallMem _ .falsum) (tr_tag_delta_l ..)))

theorem tr_step_delta_l {d} (p q : Term d) : (tr_step_m p q).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (tr_tag_delta_l ..) (.conj (tr_tag_delta_l ..) (KP.succ0_delta_l ..))))))

theorem tr_zero_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p : Term d) :
    Formula.satisfies ρ (tr_zero_m p) ↔ Tr_zero_d (p.eval ρ) := by
  simp only [tr_zero_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff, tr_tag_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨_, _, i, _, hi, hp⟩ => ⟨i, hi, hp⟩, fun ⟨i, hi, x, hp⟩ => by
    obtain ⟨a, ha, hx⟩ := (kpair_union_l M hp i).mpr (Or.inl rfl)
    exact ⟨a, ha, i, hx, hi, x, hp⟩⟩

theorem tr_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p q : Term d) :
    Formula.satisfies ρ (tr_step_m p q) ↔ Tr_step_d (p.eval ρ) (q.eval ρ) := by
  simp only [tr_step_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    tr_tag_sat_l hE, KP.succ0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨_, _, i, _, _, _, j, _, hp, hq, hs⟩ => ⟨i, j, hp, hq, hs⟩,
    fun ⟨i, j, ⟨x, hp⟩, ⟨y, hq⟩, hs⟩ => by
      obtain ⟨a, ha, hi⟩ := (kpair_union_l M hp i).mpr (Or.inl rfl)
      obtain ⟨b, hb, hj⟩ := (kpair_union_l M hq j).mpr (Or.inl rfl)
      exact ⟨a, ha, i, hi, b, hb, j, hj, ⟨x, hp⟩, ⟨y, hq⟩, hs⟩⟩

theorem tr_zero_iff_l (hE : Extensional M) {e p} (he : ∀ x, ¬ M.mem x e) :
    Tr_zero_d p ↔ Tr_tag_d e p := by
  refine ⟨fun ⟨i, hi, hp⟩ => ?_, fun h => ⟨e, he, h⟩⟩
  exact hE.eq_of_same_members i e (fun x => iff_of_false (hi x) (he x)) ▸ hp

theorem tr_step_iff_l (hE : Extensional M) {i j p q} (hp : Tr_tag_d i p) (hs : M.SuccessorOf j i) :
    Tr_step_d p q ↔ Tr_tag_d j q := by
  refine ⟨fun ⟨a, b, ha, hb, ht⟩ => ?_, fun hq => ⟨i, j, hp, hq, hs⟩⟩
  have eq := ha.unique_l hp; subst a
  exact ht.eq hE hs ▸ hb

variable {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Tr_roles_d (k f : M.Domain) : Prop := ∀ i j p,
  M.mem i k → M.SuccessorOf j i → M.PairMember I j p f → Tr_tag_d i p

def tr_roles_m {d} (k f : Term d) : Formula 1 d := set[d] ⟪∀ i ∈ ⌜k⌝ₛ, ∀ j p,
  ⌜KP.succ0_m⌝ₚ(j, i) → ⌜Formula.orderedPairMem 𝒞⌝ₚ(j, p, ⌜f⌝ₛ) → ⌜tr_tag_m⌝ₚ(i, p)⟫
derive_free_closed tr_roles_m

theorem tr_roles_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k f : Term d) :
    Formula.satisfies ρ (tr_roles_m (𝒞 := 𝒞) k f) ↔ Tr_roles_d I (k.eval ρ) (f.eval ρ) := by
  simp only [tr_roles_m, Tr_roles_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, KP.succ0_sat_l hE, Formula.satisfies_orderedPairMem_iff I,
    tr_tag_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun h i j p hi => h i hi j p, fun h i hi j p => h i j p hi⟩

theorem tr_roles_last_l (hE : Extensional M) {k l f q} (hs : M.SuccessorOf l k)
    (hf : M.IsSetFunction I f) (hq : M.PairMember I l q f) :
    Tr_roles_d I l f ↔ Tr_roles_d I k f ∧ Tr_tag_d k q := by
  constructor
  · intro h
    exact ⟨fun i j p hi => h i j p ((hs i).mpr (Or.inl hi)), h k l q hs.predecessor_mem hs hq⟩
  · rintro ⟨h, tag⟩ i j p hi hj hp
    rcases (hs i).mp hi with hi | hi
    · exact h i j p hi hj hp
    · have eq := hE.eq_of_same_members i k hi; subst i
      have eq := hj.eq hE hs; subst j
      exact (hf.2 l q p hq hp) ▸ tag

end YesMetaZFC.SetTheory.Internal

/-! ## 任意内部有限组标签角色的实际编译

首个标签检查为零，随后检查相邻标签互为后继。内部 ω 归纳证明所得单一
程序恰为所有 i<k 的标签约束；不使用外部标准性或额外的自然数常量列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Tr_prog_d (ω k m G u : M.Domain) : Prop := ∀ c X R E f,
  Smem_d I c X R → M.TransitiveSet X → M.IsFunctionSpace I E ω X → M.mem f E →
    (Ssat_d I X R E G m u f ↔ Tr_roles_d I k f)

def tr_prog_m {d} (ω k m G u : Term d) : Formula 1 d := set[d] ⟪∀ c X R E f,
  ⌜smem_m (𝒞 := 𝒞)⌝ₚ(c, X, R) → ⌜Formula.isTransitive⌝ₚ(X) →
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(E, ⌜ω⌝ₛ, X) → f ∈ E →
    (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(X, R, E, ⌜G⌝ₛ, ⌜m⌝ₛ, ⌜u⌝ₛ, f) ↔ ⌜tr_roles_m (𝒞 := 𝒞)⌝ₚ(⌜k⌝ₛ, f))⟫

@[simp] theorem tr_prog_closed_l {d} (ω k m G u : Term d)
    (hω : ω.freeSupport = []) (hk : k.freeSupport = []) (hm : m.freeSupport = [])
    (hG : G.freeSupport = []) (hu : u.freeSupport = []) : (tr_prog_m (𝒞 := 𝒞) ω k m G u).FreeClosed := by
  simp -implicitDefEqProofs [tr_prog_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hω, hk, hm, hG, hu]

theorem tr_prog_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω k m G u : Term d) :
    Formula.satisfies ρ (tr_prog_m (𝒞 := 𝒞) ω k m G u) ↔
      Tr_prog_d I (ω.eval ρ) (k.eval ρ) (m.eval ρ) (G.eval ρ) (u.eval ρ) := by
  simp only [tr_prog_m, Tr_prog_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    smem_sat_l I, Formula.satisfies_isTransitive_iff, Formula.satisfies_isFunctionSpace_iff I hE,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, ssat_sat_l I hE, tr_roles_sat_l I hE,
    Definitional.Term.eval_weaken]; rfl

theorem tr_roles_build_l (hZF : M.Models ZF) {ω k : M.Domain} (hω : M.IsOmega ω) (hk : M.mem k ω) :
    ∃ a m G u, Sformula_d I ω a m G u ∧ ∀ c X R f,
      Smem_d I c X R → M.TransitiveSet X → M.IsSetFunctionFromTo I f ω X →
        (Satisfies_d I ω c a f ↔ Tr_roles_d I k f) := by
  -- 内部自然数的零／后继分类用于选择固定语法模板，不枚举外部自然数。
  obtain ⟨Ω, hΩ, finite⟩ := KPi.exists_omega_l (ZF.models_kpi_l hZF)
  have eq := hZF.1.eq_of_same_members Ω ω (fun x => ⟨hΩ.2 ω hω.1 x, hω.2 Ω hΩ.1 x⟩)
  subst Ω
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : UnarySchema 1 := { body := .existsE (.existsE (.existsE (.conj
    (sfm_m (𝒞 := 𝒞) (.bound 4) (.bound 2) (.bound 1)) (.conj (.mem .newest (.bound 2))
      (tr_prog_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))) }
  have sat n : φ.denote ρ n ↔ ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ Tr_prog_d I ω n m G u := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      sfm_sat_l I hZF.1, Formula.satisfies_mem_iff, tr_prog_sat_l I hZF.1]; rfl
  have built : φ.denote ρ k := by
    apply hω.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω) ?_ ?_ k hk
    · intro e he
      have heω := num_mem_l hZF.1 hω (show Num_d 0 e from he)
      have empty : Sfm_d I ω e e := ⟨heω, Structure.IsSequenceOfLength.empty I he,
        fun _ _ h => h.elim fun p hp => (he p hp.2).elim⟩
      obtain ⟨m, G, add, read⟩ := sfm_eq_l I hZF hω empty heω heω
      refine (sat e).mpr ⟨m, G, e, add.program, add.root, fun c X R E f _ _ hE hf => ?_⟩
      obtain ⟨x, _, hx⟩ := ((hE f).mp hf).2.2 e heω
      exact (read X R E f x x hE hf hx hx).trans
        ⟨fun _ i _ _ hi => (he i hi).elim, fun _ => rfl⟩
    · intro n hn ih l hl
      obtain ⟨m, G, u, hG, hu, all⟩ := (sat n).mp ih
      have hlω : M.mem l ω := by
        obtain ⟨l', hl', mem⟩ := hω.1.2 n hn
        exact (hl'.eq hZF.1 hl) ▸ mem
      obtain ⟨b, hb, hbω⟩ := hω.1.2 l hlω
      -- 已有前缀固定第 n 项的标签；新检查只需读取相邻两个坐标。
      have test : ∃ ψ : Formula 1 2, ψ.FreeClosed ∧ ψ.IsDelta0 ∧ ∀ f p q,
          Tr_roles_d I n f → M.PairMember I n p f →
            (Formula.satisfies (⟨Fin.cases q (fun _ => p), fun _ => q⟩ : Env M 2) ψ ↔ Tr_tag_d n q) := by
        rcases ((finite n).mp hn).2.1 with zero | ⟨j, hj, succ⟩
        · exact ⟨tr_zero_m .newest, tr_zero_m_freeClosed _ rfl, tr_zero_delta_l _, fun _ _ q _ _ =>
            (tr_zero_sat_l hZF.1 _ _).trans (tr_zero_iff_l hZF.1 zero)⟩
        · exact ⟨tr_step_m (.bound 1) .newest, tr_step_m_freeClosed _ _ rfl rfl, tr_step_delta_l _ _,
            fun f p q roles hp => (tr_step_sat_l hZF.1 _ _ _).trans
              (tr_step_iff_l hZF.1 (roles j n p hj succ hp) succ)⟩
      obtain ⟨ψ, closed, delta, test⟩ := test
      obtain ⟨m₁, G₁, v, add, compile⟩ := source_compile_core_l I hZF hω (source_core_l ψ)
        (source_core_closed_l ψ closed) (Fin.cases l (fun _ => n)) hbω
        (Fin.cases hb.predecessor_mem (fun _ => (hb n).mpr (Or.inl hl.predecessor_mem))) hG
      obtain ⟨m₂, G₂, w, conj, both⟩ := sfm_and_l I hZF hω add.program (add.span u hu) add.root
      refine (sat l).mpr ⟨m₂, G₂, w, conj.program, conj.root, fun c X R E f model trans hE hf => ?_⟩
      have fn := (hE f).mp hf
      obtain ⟨p, hpX, hp⟩ := fn.2.2 n hn
      obtain ⟨q, hqX, hq⟩ := fn.2.2 l hlω
      let η : Env (smdl_structure_l I (R := R) model.1.2.1) 2 :=
        ⟨Fin.cases ⟨q, hqX⟩ (fun _ => ⟨p, hpX⟩), fun _ => ⟨q, hqX⟩⟩
      have atom := (compile X R model.1.2.1 E hE f hf η (Fin.cases hq (fun _ => hp))).trans
        ((source_core_sat_l ψ η).trans (smem_delta_image_l I model trans delta η))
      have env : image_env_l Subtype.val η = (⟨Fin.cases q (fun _ => p), fun _ => q⟩ : Env M 2) := by
        change Env.mk _ _ = Env.mk _ _
        congr 1
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [env] at atom
      have old := (add.sat_l I hZF hG hu X R E f).symm.trans (all c X R E f model trans hE hf)
      exact (both X R E f hf).trans ((and_congr old atom).trans
        ((and_congr_right fun prev => test f p q prev hp).trans (tr_roles_last_l I hZF.1 hl fn.1 hq).symm))
  obtain ⟨m, G, u, hG, hu, all⟩ := (sat k).mp built
  obtain ⟨a, ha⟩ := I.total G u
  have form : Sformula_d I ω a m G u := ⟨ha, hG, hu⟩
  refine ⟨a, m, G, u, form, fun c X R f model trans fn => ?_⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  exact (satisfies_decode_l I hZF.1 model.1 form hE).trans (all c X R E f model trans hE ((hE f).mpr fn))

end YesMetaZFC.SetTheory.Internal

/-! ## 标签角色成为实际完整类型中的单个查询

查询只读原元组的坐标，不加入标签常量或元组对象参数。
在 Neeman §5 的 k+2 元组上，它正是所有 i<k 的 v_(i+1)=〈i,x〉。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_roles_query_l {ω n k U D : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hk : M.mem k n) (pool : Tt_pool_d I ω n U D) : ∃ p, M.mem p D ∧
      ∀ c X R s δ t, Smem_d I c X R → M.TransitiveSet X →
        Tt_realized_d I ω c X R n s δ U D t → (M.mem p t ↔ Tr_roles_d I k s) := by
  -- 恒等名字列把原元组直接作为参数，不向常量池加入内部标签列。
  obtain ⟨N, E, names, seq, prod⟩ := pool
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
  have sat i j : φ.denote ρ i j ↔ j = i := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨e, fn, column⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := N)
    (fun i _ => ⟨i, (sat i i).mpr rfl⟩)
    (fun i _ x y hx hy => ((sat i x).mp hx).trans ((sat i y).mp hy).symm)
    (fun i j hi hj => ((sat i j).mp hj).symm ▸ (names i).mpr (Or.inl hi))
  have col i j : M.PairMember I i j e ↔ M.mem i n ∧ j = i := (column i j).trans (and_congr Iff.rfl (sat i j))
  obtain ⟨a, m, G, u, form, guard⟩ := tr_roles_build_l I hZF hω (hω.transitive (ZF.modelsKP hZF) n hn k hk)
  obtain ⟨z, code⟩ := sc_num_exists_l I hZF hω form
  obtain ⟨p, hp⟩ := (I).total z e
  have hz := sc_num_natural_l I hZF hω code
  have hpD := (prod p).mpr ⟨z, hz, e, (seq e).mpr ⟨n, hn, fn⟩, hp⟩
  refine ⟨p, hpD, fun c X R s δ t model trans type => ?_⟩
  have tuple := fn0_function_l (ZF.modelsKP hZF) type.tuple
  have ord := hω.members_areOrdinals (ZF.modelsKP hZF) n hn
  have assign : Tn_assign_d n s δ e s := by
    refine ⟨tuple.1.1, fun i x => ⟨?_, ?_⟩⟩
    · intro hx
      exact ⟨i, (col i i).mpr ⟨tuple.input_mem_of_pairMember hx, rfl⟩, Or.inl hx⟩
    · rintro ⟨j, hj, value⟩
      obtain ⟨hi, eq⟩ := (col i j).mp hj
      subst j
      obtain ⟨y, _, hy⟩ := tuple.2.2 i hi
      exact (tn_value_unique_l (ZF.modelsKP hZF) ord type.tuple value (Or.inl hy)).symm ▸ hy
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l I hZF tuple type.point
  -- k<n 保证所有被检查的 i+1 仍在原元组中，补齐赋值不改变查询。
  have bound {i j} (hi : M.mem i k) (hs : M.SuccessorOf j i) : M.mem j n := by
    apply ordinal_down_l (ZF.modelsKP hZF) (KP.successor_isOrdinal (ZF.modelsKP hZF) ((ord.mem hk).mem hi) hs) ord ?_ hk
    intro x hx
    rcases (hs x).mp hx with hx | hx
    · exact (ord.mem hk).transitive i hi x hx
    · exact (hZF.1.eq_of_same_members x i hx).symm ▸ hi
  have read i x (hi : M.mem i n) : M.PairMember I i x f ↔ M.PairMember I i x s :=
    (fill.2 i x).trans ⟨fun h => h.2.elim And.right (fun h => (h.1 hi).elim),
      fun h => ⟨hω.transitive (ZF.modelsKP hZF) n hn i hi, Or.inl ⟨hi, h⟩⟩⟩
  have roles : Tr_roles_d I k f ↔ Tr_roles_d I k s :=
    ⟨fun h i j q hi hs hq => h i j q hi hs ((read j q (bound hi hs)).mpr hq),
      fun h i j q hi hs hq => h i j q hi hs ((read j q (bound hi hs)).mp hq)⟩
  exact (type.truth p).trans ((and_iff_right hpD).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) hp hz hn fn.2.1 assign fill).trans
      ((sc_sat_decode_l I hZF hω code).trans ((guard c X R f model trans ff).trans roles))))

end YesMetaZFC.SetTheory.Internal
