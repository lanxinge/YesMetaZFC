import YesMetaZFC.Model.SetTheory.Demand.NodeScope

/-! # 双图节点查询的数值程序和实际名字列

正确性句子只带数值参数；实数前缀和节点长度留在名字列中。
编译使用任意内部有限元数，读取保留原奇偶分组及同一完整节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_node_program_d (I : kpair_convention_l.Interpretation M) (ω e l i j z : M.Domain) : Prop :=
  M.mem z ω ∧ ∀ c X R f S s k, Smem_d I c X R → M.TransitiveSet X →
    M.IsSetFunctionFromTo I f ω X → Rd_entry_d e S f → Rd_entry_d i s f → Rd_entry_d j k f →
      (Sc_sat_d I ω c z f ↔ ∃ a b, M.mem a X ∧ M.mem b X ∧
        Td_groups_d I ω e l f a b ∧ Tg_node_d I k S s a b)

def td_node_program0_m : Formula 1 6 :=
  let v : Fin 6 → Term 6 := Term.bound
  set[6] ⟪⌜v 5⌝ₛ ∈ ⌜v 0⌝ₛ ∧ (∀ c X R f S s k,
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c,X,R) → ⌜Formula.isTransitive⌝ₚ(X) →
    ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(f,⌜v 0⌝ₛ,X) →
    ⌜rd_entry0_m⌝ₚ(⌜v 1⌝ₛ,S,f) → ⌜rd_entry0_m⌝ₚ(⌜v 3⌝ₛ,s,f) → ⌜rd_entry0_m⌝ₚ(⌜v 4⌝ₛ,k,f) →
    (⌜sc_sat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 0⌝ₛ,c,⌜v 5⌝ₛ,f) ↔
      ∃ a b, a ∈ X ∧ b ∈ X ∧ ⌜td_groups_m⌝ₚ(⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 2⌝ₛ,f,a,b) ∧
        ⌜tg_node_m⌝ₚ(k,S,s,a,b)))⟫

theorem td_node_program0_closed_l : td_node_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_node_program0_m,Definitional.Formula.FreeClosed]

theorem td_node_program_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (ρ : Env M 6) : Formula.satisfies ρ td_node_program0_m ↔
      Td_node_program_d I (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) := by
  simp only [td_node_program0_m,Td_node_program_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,smem_sat_l I,
    Formula.satisfies_isTransitive_iff,Formula.satisfies_isFunctionFromTo_iff I hE,
    rd_entry0_sat_l hE,Formula.satisfies_iff_iff,sc_sat_formula_l I hE,
    Formula.satisfies_exists_iff,td_groups_sat_l I hE,tg_node_sat_l I hE,Definitional.Term.eval_weaken]
  rfl

def Td_node_code_d (n i j z p s k : M.Domain) : Prop :=
  ∃ C a b, KPair_d M p z C ∧ KPair_d M a s s ∧ KPair_d M b k k ∧
    (∀ x, M.mem x n → Rd_entry_d x x C) ∧ Rd_entry_d i a C ∧ Rd_entry_d j b C

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 编译原两组程序，其全部自由参数均为原生自然数。 -/
theorem td_node_program_l {ω e l b : M.Domain} (hw : M.IsOmega ω)
    (hl : M.mem l ω) (hb : M.mem b ω) (he : M.mem e l) (lb : M.MemberSubset l b)
    (σ : Fin 2 → M.Domain) (hs : ∀ i, M.mem (σ i) b) :
    ∃ z, Td_node_program_d I ω e l (σ 0) (σ 1) z := by
  let ρ : Env M 2 := ⟨Fin.cases e (fun _ => ω),fun _ => ω⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪¬ (⌜(.newest : Term 3)⌝ₛ = ⌜(.bound 1 : Term 3)⌝ₛ) ∧
    ⌜(Descriptive.gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(.bound 2 : Term 3)⌝ₛ,⌜(.newest : Term 3)⌝ₛ)⟫ }
  let ψ : UnarySchema 2 := { body := set[3] ⟪¬ (⌜(.newest : Term 3)⌝ₛ = ⌜(.bound 1 : Term 3)⌝ₛ) ∧
    ¬ ⌜(Descriptive.gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(.bound 2 : Term 3)⌝ₛ,⌜(.newest : Term 3)⌝ₛ)⟫ }
  obtain ⟨O,hO⟩ := ZF.separation_exists_d hZF ψ ρ l
  obtain ⟨E,hE⟩ := ZF.separation_exists_d hZF φ ρ l
  have od x : ψ.denote ρ x ↔ x ≠ e ∧ ¬ Descriptive.Gm_even_d I ω x := by
    simp only [ψ,UnarySchema.denote,Formula.satisfies_conj_iff,Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Descriptive.gm_even_sat_l I hZF.1]
    rfl
  have ev x : φ.denote ρ x ↔ x ≠ e ∧ Descriptive.Gm_even_d I ω x := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_conj_iff,Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Descriptive.gm_even_sat_l I hZF.1]
    rfl
  have odd x := (hO x).trans (and_congr_right fun _ => od x)
  have even x := (hE x).trans (and_congr_right fun _ => ev x)
  obtain ⟨a,m,G,u,form,read⟩ := td_node_build_l hZF (A := O) (B := E) hw hl hb he lb σ hs
  obtain ⟨z,code⟩ := sc_num_exists_l I hZF hw form
  refine ⟨z,sc_num_natural_l I hZF hw code,fun c X R f S s k model trans fn root real len => ?_⟩
  have groups g h : (Td_group_d I O l f g ∧ Td_group_d I E l f h) ↔ Td_groups_d I ω e l f g h := by
    have part (A y : M.Domain) (P : M.Domain → Prop)
        (ha : ∀ x, M.mem x A ↔ M.mem x l ∧ P x) :
        Td_group_d I A l f y ↔ ∀ p, M.mem p y ↔ ∃ x, M.mem x l ∧ P x ∧ Rd_entry_d x p f := by
      apply forall_congr'
      intro p
      apply iff_congr Iff.rfl
      apply exists_congr
      intro x
      exact ⟨fun ⟨hx,hA,xp⟩ => ⟨hx,((ha x).mp hA).2,xp⟩,
        fun ⟨hx,hP,xp⟩ => ⟨hx,(ha x).mpr ⟨hx,hP⟩,xp⟩⟩
    have result := and_congr (part O g _ odd) (part E h _ even)
    simp only [and_assoc] at result
    exact result
  exact (sc_sat_decode_l I hZF hw code).trans
    ((read c X R f S s k model trans fn root real len).trans
      (exists_congr fun g => exists_congr fun h => and_congr_right fun _ =>
        and_congr_right fun _ => ⟨fun ⟨a,b,c⟩ => ⟨groups g h |>.mp ⟨a,b⟩,c⟩,
          fun ⟨a,b⟩ => ⟨(groups g h |>.mpr a).1,(groups g h |>.mpr a).2,b⟩⟩))

/-- 名字列的实际成员来自完整查询池，故不额外假设列长度或名字域。 -/
theorem Td_node_program_d.query_l {ω e l i j z n U D p s k : M.Domain}
    (hw : M.IsOmega ω) (hl : M.mem l n) (he : M.mem e l)
    (program : Td_node_program_d I ω e l i j z)
    (pool : Tt_pool_d I ω n U D) (hp : M.mem p D)
    (code : Td_node_code_d n i j z p s k) : Td_node_query_d I ω e n l U D s k p := by
  obtain ⟨C,a,b,pair,sa,kb,original,si,kj⟩ := code
  obtain ⟨N,F,names,seq,prod⟩ := pool
  obtain ⟨z',hz,C',hC,cp⟩ := (prod p).mp hp
  obtain ⟨ez,eC⟩ := kpair_injective_l M cp pair
  subst z' C'
  obtain ⟨t,ht,column⟩ := (seq C).mp hC
  refine ⟨hp,fun c X R r δ T S model trans type root => ?_⟩
  have ord := hw.members_areOrdinals (ZF.modelsKP hZF) n type.finite
  obtain ⟨r₁,assign,fr₁⟩ := tn_assign_exists_l hZF ord type.tuple type.point type.constants names
    (fn0_of_function_l (ZF.modelsKP hZF) column)
  obtain ⟨f,fill,ff⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fr₁) type.point
  have value x y v (xy : Rd_entry_d x y C) (yv : Tn_value_d n r δ y v) : Rd_entry_d x v f :=
    (fill.2 x v).mpr ⟨hw.transitive (ZF.modelsKP hZF) t ht x (column.input_mem_of_pairMember xy),
      Or.inl ⟨column.input_mem_of_pairMember xy,(assign.2 x v).mpr ⟨y,xy,yv⟩⟩⟩
  have same x v (hx : M.mem x n) : Rd_entry_d x v r ↔ Rd_entry_d x v f := by
    refine ⟨fun xv => value x x v (original x hx) (Or.inl xv),fun xv => ?_⟩
    obtain ⟨y,_,xy⟩ := type.tuple.2.1 x hx
    exact ff.1.2 x y v (value x x y (original x hx) (Or.inl xy)) xv ▸ xy
  have groups g h : Td_groups_d I ω e l f g h ↔ Td_groups_d I ω e l r g h := by
    unfold Td_groups_d
    apply and_congr <;> apply forall_congr' <;> intro p <;> apply iff_congr Iff.rfl <;>
      apply exists_congr <;> intro x <;> apply and_congr_right <;> intro hx <;>
      apply and_congr_right <;> intro _ <;> apply and_congr_right <;> intro _ <;>
      exact (same x p (ord.transitive l hl x hx)).symm
  have decoded := (type.truth p).trans ((and_iff_right hp).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) pair hz ht column.2.1 assign fill).trans
      (program.2 c X R f S s k model trans ff ((same e S (ord.transitive l hl e he)).mp root)
        (value i a s si (Or.inr (Or.inr sa))) (value j b k kj (Or.inr (Or.inr kb))))))
  exact decoded.trans (exists_congr fun g => exists_congr fun h => and_congr_right fun _ =>
    and_congr_right fun _ => ⟨fun ⟨a,b⟩ => let gs := (groups g h).mp a; ⟨gs.cover_l,b,gs⟩,
      fun ⟨_,a,b⟩ => ⟨(groups g h).mpr b,a⟩⟩)

/-- 同一次编译返回完整语义和可运输列；所有参数都有实际构造。 -/
theorem td_node_query_program_l {ω e n l U D s k : M.Domain} (hw : M.IsOmega ω)
    (hn : M.mem n ω) (hl : M.mem l n) (he : M.mem e l)
    (pool : Tt_pool_d I ω n U D) (hs : M.mem s U) (hk : M.mem k U) :
    ∃ i j z p, M.mem i ω ∧ M.mem j ω ∧ Td_node_program_d I ω e l i j z ∧
      Td_node_code_d n i j z p s k ∧ Td_node_query_d I ω e n l U D s k p := by
  obtain ⟨b,σ,hb,nb,bound,_,columns⟩ := tt_column_build_l hZF hw hn 2
  have ln := (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive l hl
  obtain ⟨z,program⟩ := td_node_program_l hZF hw (hw.transitive (ZF.modelsKP hZF) n hn l hl)
    hb he (fun x hx => nb x (ln x hx)) σ bound
  obtain ⟨N,F,names,seq,prod⟩ := pool
  obtain ⟨a,sa⟩ := (I).total s s
  obtain ⟨d,kd⟩ := (I).total k k
  obtain ⟨C,column,original,params⟩ := columns U N names (Fin.cases a (fun _ => d))
    (Fin.cases ((names a).mpr (Or.inr (Or.inr ⟨s,hs,sa⟩)))
      (fun _ => (names d).mpr (Or.inr (Or.inr ⟨k,hk,kd⟩))))
  obtain ⟨p,pair⟩ := (I).total z C
  have hp := (prod p).mpr ⟨z,program.1,C,(seq C).mpr ⟨b,hb,column⟩,pair⟩
  have code : Td_node_code_d n (σ 0) (σ 1) z p s k := ⟨C,a,d,pair,sa,kd,original,params 0,params 1⟩
  exact ⟨σ 0,σ 1,z,p,hw.transitive (ZF.modelsKP hZF) b hb _ (bound 0),
    hw.transitive (ZF.modelsKP hZF) b hb _ (bound 1),program,code,
    program.query_l hZF hw hl he ⟨N,F,names,seq,prod⟩ hp code⟩

end YesMetaZFC.SetTheory.LargeCardinal
