import YesMetaZFC.Model.SetTheory.Types.SubtypeWitness
import YesMetaZFC.Model.SetTheory.Types.Embedding

/-! # 原子类型输入元组的实际重排传输

小域排列在域外按恒等延拓。随后逆向复合原实现排列，并重新构造完整
平坦赋值；原目标类型、实现模型和实现元组保持为同一组已给对象。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

/-- 任意子域上的双射在其外取恒等；不需要域是外部有限集。 -/
theorem tp_extend_l {n m ψ : M.Domain} (included : M.MemberSubset n m)
    (bij : M.IsSetBijectionFromTo Q ψ n n) :
    ∃ θ, M.IsSetBijectionFromTo Q θ m m ∧
      ∀ i j, Rd_entry_d i j θ ↔ Rd_entry_d i j ψ ∨ (M.mem i m ∧ ¬ M.mem i n ∧ j = i) := by
  classical
  let ρ : Env M 2 := ⟨Fin.cases n (fun _ => ψ),fun _ => n⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,⌜(.newest : Term 4)⌝ₛ,⌜(.bound 3 : Term 4)⌝ₛ) ∨
      (¬ (⌜(.bound 1 : Term 4)⌝ₛ ∈ ⌜(.bound 2 : Term 4)⌝ₛ) ∧
        ⌜(.newest : Term 4)⌝ₛ = ⌜(.bound 1 : Term 4)⌝ₛ)⟫ }
  have sat i j : φ.denote ρ i j ↔ Rd_entry_d i j ψ ∨ (¬ M.mem i n ∧ j = i) := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_disj_iff,rd_entry0_sat_l hZF.1,
      Formula.satisfies_conj_iff,Formula.satisfies_neg_iff,Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  obtain ⟨θ,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Q φ ρ (source := m) (target := m)
    (fun i _ => by
      by_cases hi : M.mem i n
      · obtain ⟨j,_,ij⟩ := bij.1.1.2.2 i hi
        exact ⟨j,(sat i j).mpr (Or.inl ij)⟩
      · exact ⟨i,(sat i i).mpr (Or.inr ⟨hi,rfl⟩)⟩)
    (fun i _ x y hx hy => by
      rcases (sat i x).mp hx with hx | ⟨hi,ex⟩ <;> rcases (sat i y).mp hy with hy | ⟨hj,ey⟩
      · exact bij.1.1.1.2 i x y hx hy
      · exact (hj (bij.1.1.input_mem_of_pairMember hx)).elim
      · exact (hi (bij.1.1.input_mem_of_pairMember hy)).elim
      · exact ex.trans ey.symm)
    (fun i j hi hj => ((sat i j).mp hj).elim
      (fun h => included j (bij.1.1.output_mem_of_pairMember h)) (fun h => h.2.symm ▸ hi))
  have entries i j : Rd_entry_d i j θ ↔ Rd_entry_d i j ψ ∨ (M.mem i m ∧ ¬ M.mem i n ∧ j = i) :=
    (graph i j).trans ⟨fun ⟨hi,h⟩ => ((sat i j).mp h).elim Or.inl (fun h => Or.inr ⟨hi,h⟩),
      fun h => h.elim (fun h => ⟨included i (bij.1.1.input_mem_of_pairMember h),(sat i j).mpr (Or.inl h)⟩)
        (fun ⟨hi,h⟩ => ⟨hi,(sat i j).mpr (Or.inr h)⟩)⟩
  refine ⟨θ,⟨⟨fn,?_⟩,?_⟩,entries⟩
  · intro i j x hx hy
    rcases (entries i x).mp hx with hx | ⟨_,hi,ex⟩ <;>
      rcases (entries j x).mp hy with hy | ⟨_,hj,ey⟩
    · exact bij.1.2 i j x hx hy
    · exact (hj (ey ▸ bij.1.1.output_mem_of_pairMember hx)).elim
    · exact (hi (ex ▸ bij.1.1.output_mem_of_pairMember hy)).elim
    · exact ex.symm.trans ey
  · intro j hj
    by_cases hn : M.mem j n
    · obtain ⟨i,hi,ij⟩ := bij.2 j hn
      exact ⟨i,included i hi,(entries i j).mpr (Or.inl ij)⟩
    · exact ⟨j,hj,(entries j j).mpr (Or.inr ⟨hj,hn,rfl⟩)⟩

/-- 输入元组改变排列，目标 w 和同一实现见证保持不变。 -/
theorem Ts_at_d.input_permute_l {ω δ n r s m U D w ν ψ : M.Domain}
    (witness : Ts_at_d hZF ω δ n s m U D w ν) (hw : M.IsOmega ω)
    (included : M.MemberSubset n m) (bij : M.IsSetBijectionFromTo Q ψ n n)
    (points : ∀ i j x, Rd_entry_d i j ψ → (Rd_entry_d i x r ↔ Rd_entry_d j x s)) :
    Ts_at_d hZF ω δ n r m U D w ν := by
  obtain ⟨A,c,R,t,g,h,π,rank,model,type,fg,fh,realized,original,bijπ,perm⟩ := witness
  obtain ⟨θ,bijθ,extend⟩ := tp_extend_l hZF included bij
  obtain ⟨g₀,cut⟩ := ZF.exists_restriction hZF K g m
  have fm := hw.transitive (ZF.modelsKP hZF) m type.finite
  have fg₀ := cut.isSetFunctionFromTo fg fm
  obtain ⟨θK,fθK,recode⟩ := fn_recode_l Q K hZF bijθ.1.1
  obtain ⟨v,fv,composition⟩ := ZF.exists_compositionFunction hZF K fθK fg₀
  obtain ⟨g',fill,fg'⟩ := senv_fill_exists_l K hZF fv type.point
  have filled i x (hi : M.mem i m) : M.PairMember K i x g' ↔ M.PairMember K i x v := by
    exact (fill.2 i x).trans ⟨fun h => h.2.elim And.right (fun h => (h.1 hi).elim),
      fun hx => ⟨fm i hi,Or.inl ⟨hi,hx⟩⟩⟩
  have renamed i j x (ij : Rd_entry_d i j θ) :
      M.PairMember K i x g' ↔ M.PairMember K j x g := by
    have hi := bijθ.1.1.input_mem_of_pairMember ij
    have hj := bijθ.1.1.output_mem_of_pairMember ij
    refine (filled i x hi).trans ((composition i x).trans ⟨?_,?_⟩)
    · rintro ⟨_,z,iz,zx⟩
      have eq := bijθ.1.1.1.2 i z j ((recode i z).mp iz) ij
      exact eq ▸ ((cut.2 z x).mp zx).2
    · intro hx
      exact ⟨hi,j,(recode i j).mpr ij,(cut.2 j x).mpr ⟨hj,hx⟩⟩
  have newOriginal i x (hi : M.mem i n) : Rd_entry_d i x r ↔ M.PairMember K i x g' := by
    obtain ⟨j,hj,ij⟩ := bij.1.1.2.2 i hi
    exact (points i j x ij).trans ((original j x hj).trans
      (renamed i j x ((extend i j).mpr (Or.inl ij))).symm)
  obtain ⟨θi,inverse,back⟩ := ZF.exists_inverseBijectionWithPairs hZF Q bijθ
  obtain ⟨π',fπ',composed⟩ := ZF.exists_compositionFunction hZF Q bijπ.1.1 inverse.1.1
  have bijπ' : M.IsSetBijectionFromTo Q π' m m := by
    refine ⟨⟨fπ',?_⟩,?_⟩
    · intro i j x hx hy
      obtain ⟨_,a,ia,ax⟩ := (composed i x).mp hx
      obtain ⟨_,b,jb,bx⟩ := (composed j x).mp hy
      have eq := inverse.1.2 a b x ax bx
      exact bijπ.1.2 i j a ia (eq.symm ▸ jb)
    · intro x hx
      obtain ⟨j,hj,jx⟩ := inverse.2 x hx
      obtain ⟨i,hi,ij⟩ := bijπ.2 j hj
      exact ⟨i,hi,(composed i x).mpr ⟨hi,j,ij,jx⟩⟩
  refine ⟨A,c,R,t,g',h,π',rank,model,type,fg',fh,realized,newOriginal,bijπ',fun i hi x hx => ?_⟩
  constructor
  · intro ix
    obtain ⟨j,hj,ij,jx⟩ := (perm i hi x hx).mp ix
    obtain ⟨k,hk,kj⟩ := bijθ.2 j hj
    exact ⟨k,hk,(composed i k).mpr ⟨hi,j,ij,(back j k).mpr kj⟩,(renamed k j x kj).mpr jx⟩
  · rintro ⟨k,_,ik,kx⟩
    obtain ⟨_,j,ij,jk⟩ := (composed i k).mp ik
    exact (perm i hi x hx).mpr ⟨j,bijπ.1.1.output_mem_of_pairMember ij,ij,
      (renamed k j x ((back j k).mp jk)).mp kx⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 完整实际类型对原前缀的子类型见证

沿同一个实际全赋值缩短输入前缀，保留目标完整类型、元组及恒等排列。
目标可以增加任意内部有限多个变量，不限于只增一位。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ts_at_prefix_l {ω ν A c R q m s r δ U D w : M.Domain}
    (hw : M.IsOmega ω) (rank : V_d I ν A) (model : Smem_d I c A R)
    (type : Tt_realized_d I ω c A R m r δ U D w) (sub : M.MemberSubset q m)
    (kept : ∀ i x, M.mem i q → (Rd_entry_d i x s ↔ Rd_entry_d i x r)) :
    Ts_at_d hZF ω δ q s m U D w ν := by
  obtain ⟨B,d,H,t,f,g,π,hB,lower,actual,ff,fg,graph,orig,bij,perm⟩ := ts_at_self_l hZF hw rank model type
  exact ⟨B,d,H,t,f,g,π,hB,lower,actual,ff,fg,graph,
    fun i x hi => (kept i x hi).trans (orig i x (sub i hi)),bij,perm⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 定义 3.9 的超过关系

原类型与候选类型使用同一指定常量。低层保留完整元组与实际排列，
秩间隔使用原 ν+1<η；并给出同一元组、恒等排列的实际构造入口。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tx_exceeds_d (hZF : M.Models ZF) (ω δ κ n U D u τ m V W w : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  M.mem κ τ ∧ M.MemberSubset n m ∧ ∃ η Y c R s, V_d I η Y ∧ Smem_d I c Y R ∧
    Tt_realized_d I ω c Y R n s δ U D u ∧ ∃ ν μ, M.SuccessorOf μ ν ∧ M.mem μ η ∧
      Ts_at_d hZF ω δ n s m V W w ν

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tx_exceeds_same_l {ω δ κ n U D u τ V W w η Y c R ν A d S μ s : M.Domain}
    (hω : M.IsOmega ω) (hκτ : M.mem κ τ) (hY : V_d I η Y) (upper : Smem_d I c Y R)
    (hu : Tt_realized_d I ω c Y R n s δ U D u) (hA : V_d I ν A) (lower : Smem_d I d A S)
    (hw : Tt_realized_d I ω d A S n s δ V W w) (hs : M.SuccessorOf μ ν) (hμη : M.mem μ η) :
    Tx_exceeds_d hZF ω δ κ n U D u τ n V W w :=
  ⟨hκτ, fun _ h => h, η, Y, c, R, s, hY, upper, hu, ν, μ, hs, hμη, ts_at_self_l hZF hω hA lower hw⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 超过关系的背景原公式

保留真实低层实现、全部原坐标和任意内部有限排列；高度间隙仍为 ν+1<η。
仅重写语法，既不缩减排列，也不预设新类型的最后坐标。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

def tp_perm_raw_m {d} (m A π g h : Term d) : Formula 1 d := set[d] ⟪∀ i ∈ ⌜m⌝ₛ, ∀ x ∈ ⌜A⌝ₛ,
  ⌜Formula.orderedPairMem FlatPairing.convention⌝ₚ(i, x, ⌜h⌝ₛ) ↔
    (∃ j ∈ ⌜m⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, j, ⌜π⌝ₛ) ∧ ⌜Formula.orderedPairMem FlatPairing.convention⌝ₚ(j, x, ⌜g⌝ₛ))⟫
derive_free_closed tp_perm_raw_m

theorem tp_perm_raw_sat_l {d} (ρ : Env M d) (m A π g h : Term d) :
    Formula.satisfies ρ (tp_perm_raw_m m A π g h) ↔ Tp_perm_d K
      (m.eval ρ) (A.eval ρ) (π.eval ρ) (g.eval ρ) (h.eval ρ) := by
  simp only [tp_perm_raw_m, Tp_perm_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff K,
    rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

def ts_at0_m : Formula 1 9 :=
  let p : Fin 9 → Term 9 := Term.bound
  set[9] ⟪∃ A c R r g h π,
    ⌜v_m kpair_convention_l⌝ₚ(⌜p 8⌝ₛ, A) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, A, R) ∧
    ⌜tt_realized_m⌝ₚ(⌜p 0⌝ₛ, c, A, R, ⌜p 4⌝ₛ, r, ⌜p 1⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 7⌝ₛ) ∧
    ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(g, ⌜p 0⌝ₛ, A) ∧
    ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(h, ⌜p 4⌝ₛ, A) ∧
    ⌜sx_graph_m (𝒞 := kpair_convention_l) (𝒟 := FlatPairing.convention)⌝ₚ(r, h) ∧
    (∀ i x, i ∈ ⌜p 2⌝ₛ → (⌜rd_entry0_m⌝ₚ(i, x, ⌜p 3⌝ₛ) ↔ ⌜Formula.orderedPairMem FlatPairing.convention⌝ₚ(i, x, g))) ∧
    ⌜Formula.isBijectionFromTo kpair_convention_l⌝ₚ(π, ⌜p 4⌝ₛ, ⌜p 4⌝ₛ) ∧ ⌜tp_perm_raw_m⌝ₚ(⌜p 4⌝ₛ, A, π, g, h)⟫

theorem ts_at0_closed_l : ts_at0_m.FreeClosed := by
  simp -implicitDefEqProofs [ts_at0_m, Definitional.Formula.FreeClosed]

def ts_at_m {d} (ω δ n s m U D w ν : Term d) : Formula 1 d :=
  ts_at0_m.bind (fun i => [ω, δ, n, s, m, U, D, w, ν].get i)

@[simp] theorem ts_at_closed_l {d} (ω δ n s m U D w ν : Term d)
    (hw : ω.freeSupport = []) (hδ : δ.freeSupport = []) (hn : n.freeSupport = []) (hs : s.freeSupport = [])
    (hm : m.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hu : w.freeSupport = [])
    (hν : ν.freeSupport = []) : (ts_at_m ω δ n s m U D w ν).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr ts_at0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hδ, hn, hs, hm, hU, hD, hu, hν, fun i => Fin.elim0 i⟩

theorem ts_at_sat_l {d} (ρ : Env M d) (ω δ n s m U D w ν : Term d) :
    Formula.satisfies ρ (ts_at_m ω δ n s m U D w ν) ↔ Ts_at_d hZF
      (ω.eval ρ) (δ.eval ρ) (n.eval ρ) (s.eval ρ) (m.eval ρ) (U.eval ρ) (D.eval ρ) (w.eval ρ) (ν.eval ρ) := by
  simp only [ts_at_m, Formula.satisfies_bind, ts_at0_m, Ts_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l I hZF.1, smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF),
    Formula.satisfies_isFunctionFromTo_iff K hZF.1, sx_graph_sat_l I K,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    rd_entry0_sat_l hZF.1, Formula.satisfies_orderedPairMem_iff K,
    Formula.satisfies_isBijectionFromTo_iff I hZF.1, tp_perm_raw_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

def tx_exceeds0_m : Formula 1 12 :=
  let ω := Term.bound 0; let δ := Term.bound 1; let κ := Term.bound 2; let n := Term.bound 3
  let U := Term.bound 4; let D := Term.bound 5; let u := Term.bound 6; let τ := Term.bound 7
  let m := Term.bound 8; let V := Term.bound 9; let W := Term.bound 10; let w := Term.bound 11
  set[12] ⟪
  ⌜κ⌝ₛ ∈ ⌜τ⌝ₛ ∧ ⌜n⌝ₛ ⊆ ⌜m⌝ₛ ∧ (∃ η Y c R s,
    ⌜v_m kpair_convention_l⌝ₚ(η, Y) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) ∧
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, ⌜δ⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ) ∧
    (∃ ν μ, ⌜Formula.isSuccessor⌝ₚ(μ, ν) ∧ μ ∈ η ∧
      ⌜ts_at_m⌝ₚ(⌜ω⌝ₛ, ⌜δ⌝ₛ, ⌜n⌝ₛ, s, ⌜m⌝ₛ, ⌜V⌝ₛ, ⌜W⌝ₛ, ⌜w⌝ₛ, ν)))⟫
theorem tx_exceeds0_closed_l : tx_exceeds0_m.FreeClosed := by
  simp -implicitDefEqProofs [tx_exceeds0_m, Definitional.Formula.FreeClosed]

def tx_exceeds_m {d} (ω δ κ n U D u τ m V W w : Term d) : Formula 1 d :=
  tx_exceeds0_m.bind (fun i => [ω, δ, κ, n, U, D, u, τ, m, V, W, w].get i)

@[simp] theorem tx_exceeds_closed_l {d} (ω δ κ n U D u τ m V W w : Term d)
    (hω : ω.freeSupport = []) (hδ : δ.freeSupport = []) (hκ : κ.freeSupport = []) (hn : n.freeSupport = [])
    (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hu : u.freeSupport = []) (hτ : τ.freeSupport = [])
    (hm : m.freeSupport = []) (hV : V.freeSupport = []) (hW : W.freeSupport = []) (hw : w.freeSupport = []) :
    (tx_exceeds_m ω δ κ n U D u τ m V W w).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tx_exceeds0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hω, hδ, hκ, hn, hU, hD, hu, hτ, hm, hV, hW, hw, fun i => Fin.elim0 i⟩

theorem tx_exceeds_sat_l {d} (ρ : Env M d) (ω δ κ n U D u τ m V W w : Term d) :
    Formula.satisfies ρ (tx_exceeds_m ω δ κ n U D u τ m V W w) ↔ Tx_exceeds_d hZF
      (ω.eval ρ) (δ.eval ρ) (κ.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (u.eval ρ)
      (τ.eval ρ) (m.eval ρ) (V.eval ρ) (W.eval ρ) (w.eval ρ) := by
  simp only [tx_exceeds_m, Formula.satisfies_bind, tx_exceeds0_m, Tx_exceeds_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_exists_iff, v_sat_l I hZF.1, smem_sat_l I,
    tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_isSuccessor_iff, ts_at_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal
