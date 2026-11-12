import YesMetaZFC.SetTheory.Ord.Code.Natural
import YesMetaZFC.SetTheory.InnerModel.Recursion.FunctionGraph
import YesMetaZFC.SetTheory.KP.Natural
import YesMetaZFC.SetTheory.Ord.Code.SquareCertificate
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition
import YesMetaZFC.SetTheory.Ord.OrderType

/-! # 自然数关系及一般实数的规范二值编码

在规范自然数对代码 k 处，以 k 的后继表示原图含该对，以零表示不含。
实际编码仍是 ω 上的集合函数，且落在已证明被弱见证坍塌固定的二值类中。
解码使用同一原序数配对关系，不携带任选的编号参数。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Bc_binary_d (ω b : M.Domain) : Prop := Fn0_d ω ω b ∧
  ∀ n y, Rd_entry_d n y b → (∀ t, ¬ M.mem t y) ∨ M.SuccessorOf y n

def bc_binary_m {d} (ω b : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,⌜b⌝ₛ) ∧ (∀ n ∈ ⌜ω⌝ₛ, ∀ y ∈ ⌜ω⌝ₛ,
    ⌜rd_entry0_m⌝ₚ(n,y,⌜b⌝ₛ) → ((∀ t ∈ y, ⊥) ∨ ⌜KP.succ0_m⌝ₚ(y,n)))⟫
derive_free_closed bc_binary_m

theorem bc_binary_delta_l {d} (ω b : Term d) : (bc_binary_m ω b).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
    (.disj (.forallMem _ .falsum) (KP.succ0_delta_l ..)))))

theorem bc_binary_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω b : Term d) :
    Formula.satisfies ρ (bc_binary_m ω b) ↔ Bc_binary_d (ω.eval ρ) (b.eval ρ) := by
  simp only [bc_binary_m,Formula.satisfies_conj_iff,fn0_sat_l hE,Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff,rd_entry0_sat_l hE,Formula.satisfies_disj_iff,Formula.satisfies_falsum_iff,
    KP.succ0_sat_l hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨hf,h⟩ => ⟨hf,fun n y edge => h n (hf.bound_l edge).1 y (hf.bound_l edge).2 edge⟩,
    fun h => ⟨h.1,fun n _ y _ => h.2 n y⟩⟩

def Bc_edges_d (J : kpair_convention_l.Interpretation M) (ω b r : M.Domain) : Prop :=
  ∀ n y, Rd_entry_d n y r ↔ M.mem n ω ∧ M.mem y ω ∧ ∃ k, M.mem k ω ∧ ∃ v, M.mem v ω ∧
    Oc_pair_d J n y k ∧ M.SuccessorOf v k ∧ Rd_entry_d k v b

def Bc_read_d (J : kpair_convention_l.Interpretation M) (ω b r : M.Domain) : Prop :=
  Fn0_d ω ω r ∧ Bc_edges_d J ω b r

def bc_read_m {d} (ω b r : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,⌜r⌝ₛ) ∧ (∀ n, ∀ y,
    (⌜rd_entry0_m⌝ₚ(n,y,⌜r⌝ₛ) ↔ n ∈ ⌜ω⌝ₛ ∧ y ∈ ⌜ω⌝ₛ ∧
      (∃ k ∈ ⌜ω⌝ₛ, ∃ v ∈ ⌜ω⌝ₛ, ⌜(oc_pair_m (𝒞 := kpair_convention_l))⌝ₚ(n,y,k) ∧
        ⌜KP.succ0_m⌝ₚ(v,k) ∧ ⌜rd_entry0_m⌝ₚ(k,v,⌜b⌝ₛ))))⟫
derive_free_closed bc_read_m

theorem bc_read_sat_l (J : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω b r : Term d) :
    Formula.satisfies ρ (bc_read_m ω b r) ↔ Bc_read_d J (ω.eval ρ) (b.eval ρ) (r.eval ρ) := by
  simp only [bc_read_m,Bc_read_d,Bc_edges_d,Formula.satisfies_conj_iff,fn0_sat_l hE,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,rd_entry0_sat_l hE,Formula.satisfies_mem_iff,Formula.satisfies_existsMem_iff,
    oc_pair_sat_l J hE,KP.succ0_sat_l hE,Definitional.Term.eval_weaken]
  rfl

theorem bc_read_unique_l (hKP : M.Models KP) {J : kpair_convention_l.Interpretation M} {ω b r s : M.Domain}
    (h : Bc_read_d J ω b r) (g : Bc_read_d J ω b s) : r = s :=
  (fn0_function_l hKP h.1).1.1.eq_of_pairMember_iff hKP.1 (fn0_function_l hKP g.1).1.1
    (fun n y => (h.2 n y).trans (g.2 n y).symm)

/-- 任意自然数关系都有实际二值编码；不要求它是函数图。 -/
theorem bc_edges_encode_l (hZF : M.Models ZF) {ω r : M.Domain} (hω : M.IsOmega ω)
    (fr : M.IsSetRelationOn (kp_pair_l (ZF.modelsKP hZF)) r ω) :
    ∃ b, Bc_binary_d ω b ∧ Bc_edges_d (kp_pair_l (ZF.modelsKP hZF)) ω b r := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  obtain ⟨z,hz,hzω⟩ := hω.1.1
  let active k := ∃ n, M.mem n ω ∧ ∃ y, M.mem y ω ∧ Oc_pair_d I n y k ∧ Rd_entry_d n y r
  let ρ : Env M 3 := ⟨fun i => [ω,z,r].get i,fun _ => z⟩
  let χ : Formula 1 5 := set[5] ⟪∃ n ∈ ⌜(.bound 2 : Term 5)⌝ₛ, ∃ y ∈ ⌜(.bound 2 : Term 5)⌝ₛ,
    ⌜(oc_pair_m (𝒞 := kpair_convention_l))⌝ₚ(n,y,⌜(.bound 1 : Term 5)⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(n,y,⌜(.bound 4 : Term 5)⌝ₛ)⟫
  let φ : BinarySchema 3 := {
    body := .disj (.conj χ (KP.succ0_m .newest (.bound 1)))
      (.conj (.neg χ) (Formula.extensionalEq .newest (.bound 3)))
    freeClosed := by simp -implicitDefEqProofs [χ,Definitional.Formula.FreeClosed] }
  have sat k v : φ.denote ρ k v ↔ (active k ∧ M.SuccessorOf v k) ∨ (¬ active k ∧ v = z) := by
    simp only [φ,χ,BinarySchema.denote,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_existsMem_iff,oc_pair_sat_l I hZF.1,rd_entry0_sat_l hZF.1,KP.succ0_sat_l hZF.1,
      Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,Definitional.Term.eval_weaken]
    rfl
  have total k (hk : M.mem k ω) : ∃ v, φ.denote ρ k v := by
    classical
    by_cases yes : active k
    · obtain ⟨v,hv,_⟩ := hω.1.2 k hk
      exact ⟨v,(sat k v).mpr (Or.inl ⟨yes,hv⟩)⟩
    · exact ⟨z,(sat k z).mpr (Or.inr ⟨yes,rfl⟩)⟩
  have unique k v w (hv : φ.denote ρ k v) (hw : φ.denote ρ k w) : v = w := by
    rcases (sat k v).mp hv with ⟨yes,sv⟩ | ⟨no,rfl⟩ <;>
      rcases (sat k w).mp hw with ⟨yes',sw⟩ | ⟨no',rfl⟩
    · exact Structure.SuccessorOf.eq hZF.1 sv sw
    · exact (no' yes).elim
    · exact (no yes').elim
    · rfl
  have bounded k (hk : M.mem k ω) v (hv : φ.denote ρ k v) : M.mem v ω := by
    rcases (sat k v).mp hv with ⟨_,succ⟩ | ⟨_,rfl⟩
    · obtain ⟨s,hs,hsω⟩ := hω.1.2 k hk
      exact Structure.SuccessorOf.eq hZF.1 hs succ ▸ hsω
    · exact hzω
  obtain ⟨b,fb,edges⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω)
    total (fun k _ => unique k) (fun k v hk => bounded k hk v)
  have binary : Bc_binary_d ω b := by
    refine ⟨fn0_of_function_l hKP fb,fun k v edge => ?_⟩
    rcases (sat k v).mp ((edges k v).mp edge).2 with ⟨_,succ⟩ | ⟨_,rfl⟩
    · exact Or.inr succ
    · exact Or.inl hz
  refine ⟨b,binary,fun n y => ⟨?_,?_⟩⟩
  · intro ny
    obtain ⟨hn,hy⟩ := fr.2 n y ny
    obtain ⟨k,code⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals hKP n hn) (hω.members_areOrdinals hKP y hy)
    have hk := oc_pair_natural_l I hZF hω hn hy code
    obtain ⟨v,hv,hvω⟩ := hω.1.2 k hk
    exact ⟨hn,hy,k,hk,v,hvω,code,hv,(edges k v).mpr ⟨hk,(sat k v).mpr (Or.inl ⟨⟨n,hn,y,hy,code,ny⟩,hv⟩)⟩⟩
  · rintro ⟨_,_,k,_,v,_,code,succ,edge⟩
    rcases (sat k v).mp ((edges k v).mp edge).2 with ⟨⟨a,_,c,_,code',ac⟩,_⟩ | ⟨_,eq⟩
    · obtain ⟨rfl,rfl⟩ := oc_pair_injective_l I hZF code' code
      exact ac
    · exact (hz k (eq ▸ succ.predecessor_mem)).elim

/-- 全部一般实数共用关系编码构造；函数性保留在原解码证书中。 -/
theorem bc_encode_l (hZF : M.Models ZF) {ω r : M.Domain} (hω : M.IsOmega ω) (fr : Fn0_d ω ω r) :
    ∃ b, Bc_binary_d ω b ∧ Bc_read_d (kp_pair_l (ZF.modelsKP hZF)) ω b r := by
  obtain ⟨b,binary,edges⟩ := bc_edges_encode_l hZF hω
    ⟨(fn0_function_l (ZF.modelsKP hZF) fr).1.1,fun _ _ edge => fr.bound_l edge⟩
  exact ⟨b,binary,fr,edges⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 二值解码的有界检查与实际函数构造

从给定自然数对编号图读取二值码。逐行存在唯一性、解码图和全部读取
均为 Δ₀；KP 直接构造实际解码函数。编号图是原规范方块时，读取得到
BinaryCode 中同一实数，不把图的正确性留作未经实现的抽象条件。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Bc_entry_d (ω X E b n y : M.Domain) : Prop := M.mem n ω ∧ M.mem y ω ∧
  ∃ p, M.mem p X ∧ KPair_d M p n y ∧ ∃ k, M.mem k ω ∧ Rd_entry_d p k E ∧
    ∃ v, M.mem v ω ∧ M.SuccessorOf v k ∧ Rd_entry_d k v b

def bc_entry_m {d} (ω X E b n y : Term d) : Formula 1 d := set[d] ⟪
  ⌜n⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜y⌝ₛ ∈ ⌜ω⌝ₛ ∧ (∃ p ∈ ⌜X⌝ₛ, ⌜kpair0_m⌝ₚ(p,⌜n⌝ₛ,⌜y⌝ₛ) ∧
    (∃ k ∈ ⌜ω⌝ₛ, ⌜rd_entry0_m⌝ₚ(p,k,⌜E⌝ₛ) ∧
      (∃ v ∈ ⌜ω⌝ₛ, ⌜KP.succ0_m⌝ₚ(v,k) ∧ ⌜rd_entry0_m⌝ₚ(k,v,⌜b⌝ₛ))))⟫
derive_free_closed bc_entry_m

theorem bc_entry_delta_l {d} (ω X E b n y : Term d) : (bc_entry_m ω X E b n y).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.existsMem _ (.conj (kpair0_delta_l ..)
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (.existsMem _ (.conj (KP.succ0_delta_l ..) (rd_entry0_delta_l ..))))))))

theorem bc_entry_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X E b n y : Term d) :
    Formula.satisfies ρ (bc_entry_m ω X E b n y) ↔ Bc_entry_d (ω.eval ρ) (X.eval ρ) (E.eval ρ) (b.eval ρ) (n.eval ρ) (y.eval ρ) := by
  simp only [bc_entry_m,Bc_entry_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff,kpair0_sat_l hE,rd_entry0_sat_l hE,KP.succ0_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

def Bc_valid_d (ω X E b : M.Domain) : Prop := ∀ n, M.mem n ω → ∃ y, M.mem y ω ∧
  Bc_entry_d ω X E b n y ∧ ∀ v, M.mem v ω → Bc_entry_d ω X E b n v → v = y

def bc_valid_m {d} (ω X E b : Term d) : Formula 1 d := set[d] ⟪∀ n ∈ ⌜ω⌝ₛ, ∃ y ∈ ⌜ω⌝ₛ,
  ⌜bc_entry_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜E⌝ₛ,⌜b⌝ₛ,n,y) ∧ (∀ v ∈ ⌜ω⌝ₛ,
    ⌜bc_entry_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜E⌝ₛ,⌜b⌝ₛ,n,v) → v = y)⟫
derive_free_closed bc_valid_m

theorem bc_valid_delta_l {d} (ω X E b : Term d) : (bc_valid_m ω X E b).IsDelta0 :=
  .forallMem _ (.existsMem _ (.conj (bc_entry_delta_l ..) (.forallMem _ (.imp (bc_entry_delta_l ..) (.atom _ _ _)))))

theorem bc_valid_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X E b : Term d) :
    Formula.satisfies ρ (bc_valid_m ω X E b) ↔ Bc_valid_d (ω.eval ρ) (X.eval ρ) (E.eval ρ) (b.eval ρ) := by
  simp only [bc_valid_m,Bc_valid_d,Formula.satisfies_forallMem_iff,Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_imp_iff,bc_entry_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

def Bc_graph_d (ω X E b r : M.Domain) : Prop := Fn0_d ω ω r ∧
  ∀ n, M.mem n ω → ∀ y, M.mem y ω → (Rd_entry_d n y r ↔ Bc_entry_d ω X E b n y)

def bc_graph_m {d} (ω X E b r : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,⌜r⌝ₛ) ∧ (∀ n ∈ ⌜ω⌝ₛ, ∀ y ∈ ⌜ω⌝ₛ,
    (⌜rd_entry0_m⌝ₚ(n,y,⌜r⌝ₛ) ↔ ⌜bc_entry_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜E⌝ₛ,⌜b⌝ₛ,n,y)))⟫
derive_free_closed bc_graph_m

theorem bc_graph_delta_l {d} (ω X E b r : Term d) : (bc_graph_m ω X E b r).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (bc_entry_delta_l ..))))

theorem bc_graph_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X E b r : Term d) :
    Formula.satisfies ρ (bc_graph_m ω X E b r) ↔ Bc_graph_d (ω.eval ρ) (X.eval ρ) (E.eval ρ) (b.eval ρ) (r.eval ρ) := by
  simp only [bc_graph_m,Bc_graph_d,Formula.satisfies_conj_iff,fn0_sat_l hE,Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff,rd_entry0_sat_l hE,bc_entry_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem Bc_graph_d.valid_l {ω X E b r : M.Domain} (h : Bc_graph_d ω X E b r) : Bc_valid_d ω X E b := by
  intro n hn
  obtain ⟨y,hy,ny⟩ := h.1.2.1 n hn
  exact ⟨y,hy,(h.2 n hn y hy).mp ny,fun v hv nv => h.1.2.2 n hn v hv y hy ((h.2 n hn v hv).mpr nv) ny⟩

theorem Bc_graph_d.unique_l (hE : Extensional M) {ω X E b r s : M.Domain}
    (h : Bc_graph_d ω X E b r) (g : Bc_graph_d ω X E b s) : r = s :=
  h.1.ext_l hE g.1 (fun n hn => by
    obtain ⟨y,hy,ny⟩ := h.1.2.1 n hn
    exact ⟨y,ny,(g.2 n hn y hy).mpr ((h.2 n hn y hy).mp ny)⟩)

/-- 行条件为真时，KP 的有界图构造直接给出实际解码实数。 -/
theorem bc_decode_l (hKP : M.Models KP) {ω X E b : M.Domain} (valid : Bc_valid_d ω X E b) :
    ∃ r, Bc_graph_d ω X E b r := by
  let ρ : Env M 4 := ⟨fun i => [ω,X,E,b].get i,fun _ => ω⟩
  let φ : Delta0BinarySchema 4 := {
    body := bc_entry_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 1) .newest
    delta0 := bc_entry_delta_l .. }
  have sat n y : (S1_binary.of_delta0 φ).schema.denote ρ n y ↔ Bc_entry_d ω X E b n y :=
    (S1_binary.of_delta0_sat_l ..).trans (bc_entry_sat_l hKP.1 ..)
  obtain ⟨r,fr,edge⟩ := s1_function_l hKP (.of_delta0 φ) ρ ω ω
    (fun n hn => (valid n hn).imp fun y hy => (sat n y).mpr hy.2.1)
    (fun n hn y v hy hv => by
      obtain ⟨u,_,_,unique⟩ := valid n hn
      exact (unique y ((sat n y).mp hy).2.1 ((sat n y).mp hy)).trans
        (unique v ((sat n v).mp hv).2.1 ((sat n v).mp hv)).symm)
    (fun n _ y hy => ((sat n y).mp hy).2.1)
  exact ⟨r,fr,fun n hn y _ => (edge n y).trans
    ⟨fun h => (sat n y).mp h.2,fun h => ⟨hn,(sat n y).mpr h⟩⟩⟩

/-- 有界方块读取与原全局规范配对逐项一致。 -/
theorem bc_entry_pair_l (hZF : M.Models ZF) {ω X η E b n y : M.Domain} (square : Oc_square_d ω X η E) :
    Bc_entry_d ω X E b n y ↔ M.mem n ω ∧ M.mem y ω ∧ ∃ k, M.mem k ω ∧ ∃ v, M.mem v ω ∧
      Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) n y k ∧ M.SuccessorOf v k ∧ Rd_entry_d k v b := by
  constructor
  · rintro ⟨hn,hy,p,hp,pair,k,hk,pk,v,hv,succ,kv⟩
    exact ⟨hn,hy,k,hk,v,hv,((square.codes_l hZF n y k).mpr ⟨p,hp,pair,pk⟩).1,succ,kv⟩
  · rintro ⟨hn,hy,k,hk,v,hv,code,succ,kv⟩
    obtain ⟨p,hp,pair⟩ := square.2.1.2 n hn y hy
    obtain ⟨d,_,pd⟩ := square.2.2.2.1.2.1 p hp
    have code' := ((square.codes_l hZF n y d).mpr ⟨p,hp,pair,pd⟩).1
    have eq := oc_pair_unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF code' code
    exact ⟨hn,hy,p,hp,pair,k,hk,eq ▸ pd,v,hv,succ,kv⟩

theorem bc_graph_read_l (hZF : M.Models ZF) {ω X η E b r : M.Domain} (square : Oc_square_d ω X η E) :
    Bc_graph_d ω X E b r ↔ Bc_read_d (kp_pair_l (ZF.modelsKP hZF)) ω b r := by
  constructor
  · intro h
    refine ⟨h.1,fun n y => ⟨fun ny => (bc_entry_pair_l hZF square).mp
      ((h.2 n (h.1.bound_l ny).1 y (h.1.bound_l ny).2).mp ny),fun code => ?_⟩⟩
    exact (h.2 n code.1 y code.2.1).mpr ((bc_entry_pair_l hZF square).mpr code)
  · intro h
    exact ⟨h.1,fun n _ y _ => (h.2 n y).trans (bc_entry_pair_l hZF square).symm⟩

/-- 只要求合法二值读取有实际解码图；这是一条有限句子。 -/
def Bc_closed_d (ω X E : M.Domain) : Prop := ∀ b, Fn0_d ω ω b → Bc_valid_d ω X E b → ∃ r, Bc_graph_d ω X E b r

def bc_closed_m {d} (ω X E : Term d) : Formula 1 d := set[d] ⟪∀ b,
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,b) → ⌜bc_valid_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜E⌝ₛ,b) →
    (∃ r, ⌜bc_graph_m⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜E⌝ₛ,b,r))⟫
derive_free_closed bc_closed_m

theorem bc_closed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X E : Term d) :
    Formula.satisfies ρ (bc_closed_m ω X E) ↔ Bc_closed_d (ω.eval ρ) (X.eval ρ) (E.eval ρ) := by
  simp only [bc_closed_m,Bc_closed_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    fn0_sat_l hE,bc_valid_sat_l hE,Formula.satisfies_exists_iff,bc_graph_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

end YesMetaZFC.SetTheory.Descriptive

/-! ## 可数良序的单实数编码

在严格关系中加入载体的对角线，再统一作规范二值编码。解码先恢复
完整关系，再由对角线恢复载体并删除对角线；空序及单点序同样适用。
序型始终是背景模型的原序数，不引入外部标准自然数或外部良序。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem bc_edges_decode_l {ω : M.Domain} (hw : M.IsOmega ω) (b : M.Domain) :
    ∃ R, M.IsSetRelationOn I R ω ∧ Bc_edges_d I ω b R := by
  obtain ⟨X,product⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨η,E,square⟩ := oc_square_exists_l hZF (hw.isOrdinal (ZF.modelsKP hZF)) product
  let ρ : Env M 4 := ⟨fun i => [ω,X,E,b].get i,fun _ => ω⟩
  let φ : BinarySchema 4 := { body := bc_entry_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 1) .newest }
  obtain ⟨R,rel,edges⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ ω
  have sat n y : φ.denote ρ n y ↔ Bc_entry_d ω X E b n y := bc_entry_sat_l hZF.1 ..
  refine ⟨R,rel,fun n y => (edges n y).trans ?_⟩
  exact (and_congr_right fun _ => and_congr_right fun _ => sat n y).trans
    ((Iff.intro (fun h => h.2.2) (fun h => ⟨h.1,h.2.1,h⟩)).trans (bc_entry_pair_l hZF square))

theorem bc_edges_unique_l {ω b R S : M.Domain} (rel : M.IsSetRelation I R) (rel' : M.IsSetRelation I S)
    (read : Bc_edges_d I ω b R) (read' : Bc_edges_d I ω b S) : R = S :=
  rel.eq_of_pairMember_iff hZF.1 rel' (fun i j => (read i j).trans (read' i j).symm)

def Wo_read_d (J : kpair_convention_l.Interpretation M) (ω b D R : M.Domain) : Prop :=
  ∃ U, M.IsSetRelationOn J U ω ∧ Bc_edges_d J ω b U ∧
    (∀ i, M.mem i D ↔ Rd_entry_d i i U) ∧ M.IsSetRelation J R ∧
    ∀ i j, Rd_entry_d i j R ↔ M.mem i D ∧ M.mem j D ∧ i ≠ j ∧ Rd_entry_d i j U

theorem wo_decode_l {ω : M.Domain} (hw : M.IsOmega ω) (b : M.Domain) : ∃ D R, Wo_read_d I ω b D R := by
  obtain ⟨U,rel,edges⟩ := bc_edges_decode_l hZF hw b
  let ρ : Env M 1 := ⟨fun _ => U,fun _ => U⟩
  let φ : UnarySchema 1 := { body := rd_entry0_m .newest .newest (.bound 1) }
  obtain ⟨D,sep⟩ := ZF.separation_exists_d hZF φ ρ ω
  have diag i : M.mem i D ↔ Rd_entry_d i i U := by
    have sat : φ.denote ρ i ↔ Rd_entry_d i i U := rd_entry0_sat_l hZF.1 ..
    exact (sep i).trans ((and_congr_right fun _ => sat).trans ⟨And.right,fun h => ⟨(rel.2 i i h).1,h⟩⟩)
  let ψ : BinarySchema 1 := {
    body := .conj (Formula.extensionalNe (.bound 1) .newest) (rd_entry0_m (.bound 1) .newest (.bound 2)) }
  obtain ⟨R,rr,graph⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ρ D
  have sat i j : ψ.denote ρ i j ↔ i ≠ j ∧ Rd_entry_d i j U := by
    simp only [ψ,BinarySchema.denote,Formula.satisfies_conj_iff,Formula.extensionalNe,
      Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,rd_entry0_sat_l hZF.1]
    rfl
  exact ⟨D,R,U,rel,edges,diag,rr.1,fun i j => (graph i j).trans
    (and_congr_right fun _ => and_congr_right fun _ => sat i j)⟩

theorem Wo_read_d.unique_l {ω b D R D' R' : M.Domain}
    (read : Wo_read_d I ω b D R) (read' : Wo_read_d I ω b D' R') : D = D' ∧ R = R' := by
  obtain ⟨U,rel,edges,diag,rr,graph⟩ := read
  obtain ⟨U',rel',edges',diag',rr',graph'⟩ := read'
  have eq := bc_edges_unique_l hZF rel.1 rel'.1 edges edges'
  subst U'
  have eD : D = D' := hZF.1.eq_of_same_members _ _ (fun i => (diag i).trans (diag' i).symm)
  subst D'
  exact ⟨rfl,rr.eq_of_pairMember_iff hZF.1 rr' (fun i j => (graph i j).trans (graph' i j).symm)⟩

/-- 任意内部可数严格关系的载体和边同时进入一个实际二值实数。 -/
theorem wo_encode_l {ω D R : M.Domain} (hw : M.IsOmega ω) (sub : M.MemberSubset D ω)
    (rel : M.IsSetRelationOn I R D) (irrefl : ∀ i, M.mem i D → ¬ Rd_entry_d i i R) :
    ∃ b, Bc_binary_d ω b ∧ Wo_read_d I ω b D R := by
  let ρ : Env M 2 := ⟨fun i => [D,R].get i,fun _ => ω⟩
  let φ : BinarySchema 2 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 2)) (Formula.extensionalEq (.bound 1) .newest))
      (rd_entry0_m (.bound 1) .newest (.bound 3)) }
  obtain ⟨U,ur,graph⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ ω
  have sat i j : φ.denote ρ i j ↔ (M.mem i D ∧ i = j) ∨ Rd_entry_d i j R := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,rd_entry0_sat_l hZF.1]
    rfl
  have edges i j : Rd_entry_d i j U ↔ (M.mem i D ∧ i = j) ∨ Rd_entry_d i j R := by
    apply (graph i j).trans
    exact ⟨fun h => (sat i j).mp h.2.2,fun h => by
      have hi : M.mem i D := h.elim And.left (fun edge => (rel.2 i j edge).1)
      have hj : M.mem j D := h.elim (fun h => h.2 ▸ h.1) (fun edge => (rel.2 i j edge).2)
      exact ⟨sub i hi,sub j hj,(sat i j).mpr h⟩⟩
  obtain ⟨b,binary,read⟩ := bc_edges_encode_l hZF hw ur
  refine ⟨b,binary,U,ur,read,fun i => ?_,rel.1,fun i j => ?_⟩
  · exact ⟨fun hi => (edges i i).mpr (Or.inl ⟨hi,rfl⟩),fun h =>
      ((edges i i).mp h).elim And.left (fun edge => (irrefl i (rel.2 i i edge).1 edge).elim)⟩
  · constructor
    · intro edge
      exact ⟨(rel.2 i j edge).1,(rel.2 i j edge).2,
        fun eq => irrefl i (rel.2 i j edge).1 (eq.symm ▸ edge),(edges i j).mpr (Or.inr edge)⟩
    · rintro ⟨_,_,ne,ij⟩
      exact ((edges i j).mp ij).elim (fun h => (ne h.2).elim) id

def Wo_code_d (J : kpair_convention_l.Interpretation M) (ω b β : M.Domain) : Prop :=
  Bc_binary_d ω b ∧ ∃ D R, Wo_read_d J ω b D R ∧
    M.IsSetCodedWellOrder J R D ∧ M.IsWellOrderType J R D β

/-- 实际计数单射先生产原序型的良序副本，再合并载体与边，得到一个吸收实数。 -/
theorem wo_code_exists_l {ω β : M.Domain} (hw : M.IsOmega ω) (hβ : M.IsOrdinal β)
    (count : M.CardinalLessOrEqual I β ω) : ∃ b, Wo_code_d I ω b β := by
  obtain ⟨f,inj⟩ := count
  obtain ⟨D,R,sub,rel,order,type⟩ := ZF.exists_wellOrderRealization_of_ordinalInjection hZF I hβ inj
  obtain ⟨b,binary,read⟩ := wo_encode_l hZF hw sub rel order.linear.2.1.1
  exact ⟨b,binary,D,R,read,order,type⟩

end YesMetaZFC.SetTheory.Descriptive
