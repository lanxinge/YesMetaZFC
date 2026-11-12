import YesMetaZFC.SetTheory.LargeCardinal.Demand.Parameters
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Depth
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Game.RootSquare
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RealTrace
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion

/-! # demanding 原历史中的请求与回答对应

八个坐标为时钟、零、一、轮号、历史、节点长度、回答秩高和原类型。
事件使用所属模型的完整历史；共同低层只负责最后三个坐标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_trace_d (I : kpair_convention_l.Interpretation M) (c e a n h k τ w : M.Domain) : Prop :=
  ∃ v ℓ κ u b, Tg_event_d I c n e h v ∧ Td_move_d v ℓ k κ u ∧
    Tg_event_d I c n a h b ∧ KPair_d M b τ w

def td_trace_m {d} (c e a n h k τ w : Term d) : Formula 1 d := set[d] ⟪
  ∃ v ℓ κ u b, ⌜tg_event_m⌝ₚ(⌜c⌝ₛ,⌜n⌝ₛ,⌜e⌝ₛ,⌜h⌝ₛ,v) ∧
    ⌜td_move_m⌝ₚ(v,ℓ,⌜k⌝ₛ,κ,u) ∧ ⌜tg_event_m⌝ₚ(⌜c⌝ₛ,⌜n⌝ₛ,⌜a⌝ₛ,⌜h⌝ₛ,b) ∧
    ⌜kpair0_m⌝ₚ(b,⌜τ⌝ₛ,⌜w⌝ₛ)⟫
derive_free_closed td_trace_m

def td_trace0_m : Formula 1 8 :=
  td_trace_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)

theorem td_trace0_closed_l : td_trace0_m.FreeClosed := by simp -implicitDefEqProofs [td_trace0_m]

theorem td_trace_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (c e a n h k τ w : Term d) :
    Formula.satisfies ρ (td_trace_m c e a n h k τ w) ↔
      Td_trace_d I (c.eval ρ) (e.eval ρ) (a.eval ρ) (n.eval ρ) (h.eval ρ)
        (k.eval ρ) (τ.eval ρ) (w.eval ρ) := by
  simp only [td_trace_m,Td_trace_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    tg_event_sat_l I hE,td_move_sat_l hE,kpair0_sat_l hE,Definitional.Term.eval_weaken]
  rfl

theorem Td_trace_d.mono_l (I : kpair_convention_l.Interpretation M) {c e a n h h' k τ w : M.Domain}
    (trace : Td_trace_d I c e a n h k τ w) (sub : M.MemberSubset h h') :
    Td_trace_d I c e a n h' k τ w := by
  obtain ⟨v,ℓ,κ,u,b,request,move,answer,pair⟩ := trace
  exact ⟨v,ℓ,κ,u,b,request.mono_l I sub,move,answer.mono_l I sub,pair⟩

variable (I : kpair_convention_l.Interpretation M)

def Td_trace_at_d (N R c e a n h k τ w : M.Domain) : Prop :=
  Rr_truth_d I N R td_trace0_m (fun i => [c,e,a,n,h,k,τ,w].get i)

theorem td_trace_native_l {N R : M.Domain} (nx : ∃ x, M.mem x N)
    (hN : (smdl_structure_l I (R := R) nx).Models KP)
    (v : Env (smdl_structure_l I (R := R) nx) 8) :
    Td_trace_at_d I N R (v.bound 0).val (v.bound 1).val (v.bound 2).val (v.bound 3).val
      (v.bound 4).val (v.bound 5).val (v.bound 6).val (v.bound 7).val ↔
    Td_trace_d (kp_pair_l hN) (v.bound 0) (v.bound 1) (v.bound 2) (v.bound 3)
      (v.bound 4) (v.bound 5) (v.bound 6) (v.bound 7) := by
  have values : (fun i : Fin 8 => (v.bound i).val) =
      (fun i => [(v.bound 0).val,(v.bound 1).val,(v.bound 2).val,(v.bound 3).val,
        (v.bound 4).val,(v.bound 5).val,(v.bound 6).val,(v.bound 7).val].get i) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))) i
  change Rr_truth_d I N R td_trace0_m _ ↔ _
  exact (iff_of_eq (congrArg (Rr_truth_d I N R td_trace0_m) values.symm)).trans
    ((rr_truth_native_l I nx td_trace0_m td_trace0_closed_l v.bound).trans
    ((Formula.closed_env_l td_trace0_m td_trace0_closed_l (ρ := ⟨v.bound,fun _ => v.bound 0⟩)
      (η := v) rfl).trans (td_trace_sat_l (kp_pair_l hN) hN.1 v ..)))

/-- 实际父边搬运整份历史，数字图保证背景档案行号保持不变。 -/
theorem Td_trace_at_d.image_l (hZF : M.Models ZF)
    {Ω cN N R cP P S j w z w' z' c e a h c' e' a' h' m n k τ u : M.Domain}
    (hΩ : M.IsOmega Ω) (mn : Smdl_d I cN N R) (mp : Smdl_d I cP P S)
    (map : Smap_d I Ω cN cP N P j) (en : Rf_ext_d I N R) (ep : Rf_ext_d I P S)
    (numbers : Rr_layer_d I Ω N R w z) (numbers' : Rr_layer_d I Ω P S w' z')
    (points : ∀ i : Fin 4, M.PairMember I ([c,e,a,h].get i) ([c',e',a',h'].get i) j)
    (index : M.PairMember I m n z) (trace : Td_trace_at_d I N R c e a n h k τ u) :
    ∃ n' k' τ' u', M.PairMember I m n' z' ∧
      M.PairMember I k k' j ∧ M.PairMember I τ τ' j ∧ M.PairMember I u u' j ∧
      Td_trace_at_d I P S c' e' a' n' h' k' τ' u' := by
  have members := trace.1
  obtain ⟨n',hn,inn⟩ := map.1.1.2.2 n (members 3)
  obtain ⟨k',hk,ik⟩ := map.1.1.2.2 k (members 5)
  obtain ⟨τ',hτ,iτ⟩ := map.1.1.2.2 τ (members 6)
  obtain ⟨u',hu,iu⟩ := map.1.1.2.2 u (members 7)
  have digits := (numbers.omega_map_l I hZF hΩ mn mp map en ep numbers').2
  obtain ⟨n₀,_,in₀⟩ := numbers'.injection.1.2.2 m (numbers.injection.1.input_mem_of_pairMember index)
  have eq := map.1.1.1.2 n n₀ n' (digits m n n₀ index in₀) inn
  exact ⟨n',k',τ',u',eq ▸ in₀,ik,iτ,iu,
    trace.map_l I hZF hΩ mn mp map td_trace0_closed_l
      (Fin.cases (points 0) (Fin.cases (points 1) (Fin.cases (points 2) (Fin.cases inn
        (Fin.cases (points 3) (Fin.cases ik (Fin.cases iτ (Fin.cases iu (fun i => Fin.elim0 i)))))))))⟩

/-- 原生历史增长不重新选择任何请求或回答。 -/
theorem Td_trace_at_d.mono_l {cN N R c e a n h h' k τ w : M.Domain}
    (mn : Smdl_d I cN N R) (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (trace : Td_trace_at_d I N R c e a n h k τ w) (member : M.mem h' N)
    (sub : ∀ x, M.mem x N → M.PairMember I x h R → M.PairMember I x h' R) :
    Td_trace_at_d I N R c e a n h' k τ w := by
  let Nn := smdl_structure_l I (R := R) mn.2.1
  let v : Fin 8 → M.Domain := fun i => [c,e,a,n,h,k,τ,w].get i
  let ρ : Env Nn 8 := ⟨fun i => ⟨v i,trace.1 i⟩,fun _ => ⟨c,trace.1 0⟩⟩
  let η : Env Nn 8 := ⟨fun i => [ρ.bound 0,ρ.bound 1,ρ.bound 2,ρ.bound 3,
    ⟨h',member⟩,ρ.bound 5,ρ.bound 6,ρ.bound 7].get i,ρ.free⟩
  exact (td_trace_native_l I mn.2.1 hN η).mpr
    (((td_trace_native_l I mn.2.1 hN ρ).mp trace).mono_l (kp_pair_l hN)
      (fun x hx => sub x.val x.property hx))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 幂集代码产生 demanding 字母枚举

内部字母编码与原幂集的实际可数载体，直接产生全部字母的可数载体和
调度所需满射。不再单独假定字母像可数；子集字母族有现成的包含编码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_power_enum_l {Ω X R B : M.Domain} (nx : ∃ x, M.mem x X)
    (hN : (smdl_structure_l I (R := R) nx).Models KP)
    (U P z : (smdl_structure_l I (R := R) nx).Domain)
    (carrier : ∀ x, M.mem x B ↔ M.mem x X ∧ Rd_entry_d x P.val R)
    (count : M.CardinalLessOrEqual I B Ω)
    (code : (smdl_structure_l I (R := R) nx).CardinalLessOrEqual (kp_pair_l hN) U P)
    (chosen : (smdl_structure_l I (R := R) nx).mem z U) :
    ∃ A E, (∀ x, M.mem x A ↔ M.mem x X ∧ Rd_entry_d x U.val R) ∧
      M.CardinalLessOrEqual I A Ω ∧ Td_enum_d Ω X R U.val E := by
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨A,hA⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases U.val (fun _ => R),fun _ => X⟩ X
  have letters x : M.mem x A ↔ M.mem x X ∧ Rd_entry_d x U.val R :=
    (hA x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  obtain ⟨j,hj⟩ := rr_cardinal_bound_l hZF nx hN U P letters carrier code
  obtain ⟨k,hk⟩ := count
  have small := ZF.exists_compositionInjection hZF I hj hk
  obtain ⟨E,enum⟩ := td_enum_l hZF letters small z.property chosen
  exact ⟨A,E,letters,small,enum⟩

/-- 实际子集族使用包含单射，无须另外给出编码函数。 -/
theorem td_subset_enum_l {Ω X R B : M.Domain} (nx : ∃ x, M.mem x X)
    (native : (smdl_structure_l I (R := R) nx).Models ZF)
    (U P z : (smdl_structure_l I (R := R) nx).Domain)
    (carrier : ∀ x, M.mem x B ↔ M.mem x X ∧ Rd_entry_d x P.val R)
    (count : M.CardinalLessOrEqual I B Ω)
    (sub : (smdl_structure_l I (R := R) nx).MemberSubset U P)
    (chosen : (smdl_structure_l I (R := R) nx).mem z U) :
    ∃ A E, (∀ x, M.mem x A ↔ M.mem x X ∧ Rd_entry_d x U.val R) ∧
      M.CardinalLessOrEqual I A Ω ∧ Td_enum_d Ω X R U.val E :=
  td_power_enum_l hZF nx (ZF.modelsKP native) U P z carrier count
    (ZF.exists_inclusionInjection native (kp_pair_l (ZF.modelsKP native)) sub) chosen

/-- 只记录同一树的最小第一字母域可编码于 δ 的幂集，便于沿原边整体运输。 -/
def td_code_m {d} (S δ : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE
    (.conj (td_alphabet_m S.weaken.weaken.weaken (.bound 2) (.bound 1))
      (.conj (Formula.isPowerSet .newest δ.weaken.weaken.weaken)
        (Formula.cardinalLessOrEqual kpair_convention_l (.bound 2) .newest)))))
derive_free_closed td_code_m

theorem td_code_sat_l {N : Structure.{u}} (hN : N.Models KP) {d} (ρ : Env N d) (S δ : Term d) :
    Formula.satisfies ρ (td_code_m S δ) ↔
      ∃ U V P, Td_alphabet_d (S.eval ρ) U V ∧ N.IsPowerSetOf P (δ.eval ρ) ∧
        N.CardinalLessOrEqual (kp_pair_l hN) U P := by
  simp only [td_code_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    td_alphabet_sat_l hN.1,Formula.satisfies_isPowerSet_iff,
    Formula.satisfies_cardinalLessOrEqual_iff (kp_pair_l hN) hN.1,Definitional.Term.eval_weaken]
  rfl

def Td_code_d (J : kpair_convention_l.Interpretation M) (X R S δ : M.Domain) : Prop :=
  Rr_truth_d J (n := 1) X R (td_code_m (.bound 0) (.bound 1)) (Fin.cases S (fun _ => δ))

/-- 初始模型内的实际字母单射产生编码不变量。 -/
theorem td_code_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (hN : (smdl_structure_l I (R := R) nx).Models KP)
    (S δ U V P : (smdl_structure_l I (R := R) nx).Domain)
    (alphabet : Td_alphabet_d S U V) (power : (smdl_structure_l I (R := R) nx).IsPowerSetOf P δ)
    (code : (smdl_structure_l I (R := R) nx).CardinalLessOrEqual (kp_pair_l hN) U P) :
    Td_code_d I X R S.val δ.val := by
  let v : Fin 2 → (smdl_structure_l I (R := R) nx).Domain := Fin.cases S (fun _ => δ)
  have truth := (rr_truth_native_l I nx (td_code_m (.bound 0) (.bound 1))
    (by simp -implicitDefEqProofs) v).mpr
      ((td_code_sat_l hN ⟨v,fun _ => S⟩ (.bound 0) (.bound 1)).mpr ⟨U,V,P,alphabet,power,code⟩)
  have values : (fun i => (v i).val) = Fin.cases S.val (fun _ => δ.val) :=
    funext (Fin.cases rfl (fun _ => rfl))
  rw [values] at truth
  exact truth

theorem Td_code_d.map_l {Ω c d X R Y T j S δ S' δ' : M.Domain}
    (hΩ : M.IsOmega Ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y T)
    (map : Smap_d I Ω c d X Y j) (code : Td_code_d I X R S δ)
    (tree : Rd_entry_d S S' j) (ordinal : Rd_entry_d δ δ' j) : Td_code_d I Y T S' δ' :=
  Rr_truth_d.map_l I hZF hΩ mx my map (by simp -implicitDefEqProofs) code
    (Fin.cases tree (fun _ => ordinal))

/-- 幂集计数与内部编码共同控制目标的全部字母，包括非旧像的字母。 -/
theorem Td_code_d.enum_l {Ω X R : M.Domain} (nx : ∃ x, M.mem x X)
    (hN : (smdl_structure_l I (R := R) nx).Models KP)
    (S δ U V z : (smdl_structure_l I (R := R) nx).Domain)
    (code : Td_code_d I X R S.val δ.val)
    (count : Pc_count_d I Ω X R δ.val) (alphabet : Td_alphabet_d S U V)
    (chosen : (smdl_structure_l I (R := R) nx).mem z U) :
    ∃ A E, (∀ x, M.mem x A ↔ M.mem x X ∧ Rd_entry_d x U.val R) ∧
      M.CardinalLessOrEqual I A Ω ∧ Td_enum_d Ω X R U.val E := by
  let v : Fin 2 → (smdl_structure_l I (R := R) nx).Domain := Fin.cases S (fun _ => δ)
  have values : (fun i => (v i).val) = Fin.cases S.val (fun _ => δ.val) :=
    funext (Fin.cases rfl (fun _ => rfl))
  have truth := (rr_truth_native_l I nx (td_code_m (.bound 0) (.bound 1))
    (by simp -implicitDefEqProofs) v).mp (values.symm ▸ code)
  obtain ⟨U',V',P',alphabet',power',coding⟩ :=
    (td_code_sat_l hN ⟨v,fun _ => S⟩ (.bound 0) (.bound 1)).mp truth
  obtain ⟨P,B,power,carrier,small⟩ := count.native_l hZF nx δ
  have eu := (alphabet'.ext_l hN.1 alphabet).1
  have ep : P' = P := hN.1.eq_of_same_members _ _
    (fun x => (power' x).trans (power x).symm)
  exact td_power_enum_l hZF nx hN U P z carrier small (eu ▸ ep ▸ coding) chosen

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 原回合的实际档案

每行将原模型、根图、支撑、数字图、深度调度和完整六十二槽回合打包为背景集合。
源行始终不变，并保存其字母域与树来自同一初始对象的像关系；当前共同图、
端点界及历史对应随实际原边更新。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} {Ar Sr : M.Domain}

structure Td_archive_row_d (α : Type u) where
  v : Fin 62 → α
  i : α
  c : α
  X : α
  R : α
  p : α
  L : α
  U : α
  z : α
  depth : α
  ancestors : α
  enumeration : α

def Td_archive_row_d.values_d {α : Type u} (s : Td_archive_row_d α) : Fin 73 → α :=
  Fin.addCases (m := 62) (n := 11) s.v
    (fun i => [s.i,s.c,s.X,s.R,s.p,s.L,s.U,s.z,s.depth,s.ancestors,s.enumeration].get i)

theorem Td_archive_row_d.eq_l {a b : Td_archive_row_d M.Domain}
    (h : a.values_d = b.values_d) : a = b := by
  have hv : a.v = b.v := funext fun i => by
    simpa only [Td_archive_row_d.values_d,Fin.addCases_left] using congrFun h (i.castAdd 11)
  have hi := congrFun h 62
  have hc := congrFun h 63
  have hX := congrFun h 64
  have hR := congrFun h 65
  have hp := congrFun h 66
  have hL := congrFun h 67
  have hU := congrFun h 68
  have hz := congrFun h 69
  have hd := congrFun h 70
  have hF := congrFun h 71
  have hE := congrFun h 72
  cases a
  cases b
  congr 1 <;> assumption

variable (I : kpair_convention_l.Interpretation M)

structure Td_archive_source_d (Ω c₀ X₀ Ar Sr D₀ : M.Domain) (s : Td_archive_row_d M.Domain) : Prop where
  model : Smdl_d I s.c s.X s.R
  origin : Smap_d I Ω c₀ s.c X₀ s.X s.p
  round : Rr_truth_d I s.X s.R td_round0_m s.v
  numbers : Rr_layer_d I Ω s.X s.R (s.v 19) s.z
  below : M.PairMember I (s.v 0) s.L s.R
  small : Rr_small_d I s.X s.R s.U
  cofinal : Tg_raw_cofinal_d I (s.v 19) s.X s.R s.L
  depth : Td_depth_d I Ω s.X s.R (s.v 47) s.depth s.ancestors
  enumeration : Td_enum_d Ω s.X s.R (s.v 47) s.enumeration
  chosen : Td_pick_d I Ω s.depth s.ancestors (s.v 49)
  /-- 原根切片在本轮类型的秩层内；下一次选中本行时恢复临界点以下的方块。 -/
  root_low : ∀ a x, M.mem a D₀ → Rd_entry_d a x s.p → Rd_entry_d x (s.v 1) s.R
  letters_root : Rd_entry_d Ar (s.v 50) s.p
  tree_root : Rd_entry_d Sr (s.v 22) s.p
  /-- 被选作后续父模型时，使用该原模型自己的幂集计数。 -/
  power_count : Pc_count_d I Ω s.X s.R (s.v 21)
  support_below : Rd_entry_d s.L (s.v 21) s.R
  alphabet_code : Td_code_d I s.X s.R (s.v 22) (s.v 21)

def Td_archive_view_d (v : Fin 62 → M.Domain) (g N R c e a z h m : M.Domain) : Prop :=
  ∃ n k τ w, M.PairMember I m n z ∧ M.PairMember I (v 25) k g ∧
    M.PairMember I (v 0) τ g ∧ M.PairMember I (v 4) w g ∧
    Td_trace_at_d I N R c e a n h k τ w ∧
    ∃ s, M.PairMember I (v 44) s g ∧ Td_play_at_d I N R c a h s

def Td_archive_entry_d (Ω c₀ X₀ Ar Sr N R χ c e a z h m r D₀ q : M.Domain) : Prop :=
  ∃ s : Td_archive_row_d M.Domain, Rt_tuple_d s.values_d r ∧ Td_archive_source_d I Ω c₀ X₀ Ar Sr D₀ s ∧
    ∃ l V Δ g, Ic_common_d I s.X s.R N R s.L l s.U V Δ g ∧
      (M.PairMember I l χ R ∨ l = χ) ∧ Tg_root_square_d D₀ s.p q g ∧
        Td_archive_view_d I s.v g N R c e a z h m

def Td_archive_d (Ω c₀ X₀ Ar Sr D N R χ c e a z h D₀ q : M.Domain) : Prop :=
  ∀ m r, M.PairMember I m r D → Td_archive_entry_d I Ω c₀ X₀ Ar Sr N R χ c e a z h m r D₀ q

/-- 空集同时给出零长档案函数与全部对应的初始实例。 -/
theorem td_archive_empty_l {Ω c₀ X₀ D N R χ c e a z h D₀ q : M.Domain}
    (empty : ∀ x, ¬ M.mem x D) :
    M.IsSequenceOfLength I D D ∧ Td_archive_d I Ω c₀ X₀ Ar Sr D N R χ c e a z h D₀ q := by
  refine ⟨Structure.IsSequenceOfLength.empty I empty,?_⟩
  rintro m r ⟨p,_,hp⟩
  exact (empty p hp).elim

/-- 同一实际行码读回原六十二槽及已选共同图，无需重新证明事件对应。 -/
theorem Td_archive_entry_d.read_l {Ω c₀ X₀ N R χ c e a z h m r D₀ q : M.Domain}
    (entry : Td_archive_entry_d I Ω c₀ X₀ Ar Sr N R χ c e a z h m r D₀ q)
    {s : Td_archive_row_d M.Domain} (code : Rt_tuple_d s.values_d r) :
    Td_archive_source_d I Ω c₀ X₀ Ar Sr D₀ s ∧
    ∃ l V Δ g, Ic_common_d I s.X s.R N R s.L l s.U V Δ g ∧
      (M.PairMember I l χ R ∨ l = χ) ∧ Tg_root_square_d D₀ s.p q g ∧
        Td_archive_view_d I s.v g N R c e a z h m := by
  obtain ⟨s',code',rest⟩ := entry
  exact Td_archive_row_d.eq_l (rt_tuple_inj_l code' code) ▸ rest

/-- 数字图只识别档案轮号；请求与回答从当前模型中的同一历史直接读出。 -/
theorem Td_archive_view_d.read_l {cN N R g z m : M.Domain} {v : Fin 62 → M.Domain}
    (mn : Smdl_d I cN N R) (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (c e a n h : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (view : Td_archive_view_d I v g N R c.val e.val a.val z h.val m)
    (numbers : M.IsSetFunction I z) (index : M.PairMember I m n.val z) :
    ∃ k τ w : (smdl_structure_l I (R := R) mn.2.1).Domain,
      Td_trace_d (kp_pair_l hN) c e a n h k τ w ∧
      (∀ i : Fin 3, M.PairMember I (v ([25,0,4].get i)) ([k,τ,w].get i).val g) := by
  obtain ⟨n',k,τ,w,idx,ik,iτ,iw,trace,_⟩ := view
  have eq := numbers.2 m n' n.val idx index
  subst n'
  let kn := (⟨k,trace.1 5⟩ : (smdl_structure_l I (R := R) mn.2.1).Domain)
  let τn := (⟨τ,trace.1 6⟩ : (smdl_structure_l I (R := R) mn.2.1).Domain)
  let wn := (⟨w,trace.1 7⟩ : (smdl_structure_l I (R := R) mn.2.1).Domain)
  let ρ : Env (smdl_structure_l I (R := R) mn.2.1) 8 :=
    ⟨fun i => [c,e,a,n,h,kn,τn,wn].get i,fun _ => c⟩
  exact ⟨kn,τn,wn,(td_trace_native_l I mn.2.1 hN ρ).mp trace,
    Fin.cases ik (Fin.cases iτ (Fin.cases iw (fun i => Fin.elim0 i)))⟩

/-- 任意真实历史延长保持整列旧对应，涵盖回答、实数落子与下一请求。 -/
theorem Td_archive_d.mono_l {Ω c₀ X₀ D cN N R χ c e a z h h' D₀ q : M.Domain}
    (old : Td_archive_d I Ω c₀ X₀ Ar Sr D N R χ c e a z h D₀ q)
    (mn : Smdl_d I cN N R) (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (member : M.mem h' N)
    (sub : ∀ x, M.mem x N → M.PairMember I x h R → M.PairMember I x h' R) :
    Td_archive_d I Ω c₀ X₀ Ar Sr D N R χ c e a z h' D₀ q := by
  intro m r hr
  obtain ⟨s,code,source,l,V,Δ,g,common,bound,roots,n,k,τ,w,index,ik,iτ,iw,trace,t,point,play⟩ := old m r hr
  exact ⟨s,code,source,l,V,Δ,g,common,bound,roots,n,k,τ,w,index,ik,iτ,iw,
    trace.mono_l I mn hN member sub,t,point,play.mono_l I mn hN member sub⟩

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

/-- 一次实际父边与已复合共同图使用同一批像，轮号不被重置。 -/
theorem Td_archive_view_d.image_l
    {Ω cN N R cP P S j w z w' z' c e a h c' e' a' h' m g g' : M.Domain}
    {v : Fin 62 → M.Domain}
    (view : Td_archive_view_d J v g N R c e a z h m)
    (hΩ : M.IsOmega Ω) (mn : Smdl_d J cN N R) (mp : Smdl_d J cP P S)
    (map : Smap_d J Ω cN cP N P j) (en : Rf_ext_d J N R) (ep : Rf_ext_d J P S)
    (numbers : Rr_layer_d J Ω N R w z) (numbers' : Rr_layer_d J Ω P S w' z')
    (points : ∀ i : Fin 4, Rd_entry_d ([c,e,a,h].get i) ([c',e',a',h'].get i) j)
    (square : ∀ x y E, Rd_entry_d x y g → (Rd_entry_d x E g' ↔ Rd_entry_d y E j)) :
    Td_archive_view_d J v g' P S c' e' a' z' h' m := by
  obtain ⟨n,k,τ,u,index,ik,iτ,iu,trace,s,is,play⟩ := view
  obtain ⟨n',k',τ',u',index',kk,ττ,uu,moved⟩ :=
    trace.image_l J hZF hΩ mn mp map en ep numbers numbers' points index
  obtain ⟨s',ss,played⟩ := play.image_l J hZF hΩ mn mp map
    (Fin.cases (points 0) (Fin.cases (points 2) (Fin.cases (points 3) (fun i => Fin.elim0 i))))
  exact ⟨n',k',τ',u',index',(square _ _ _ ik).mpr kk,
    (square _ _ _ iτ).mpr ττ,(square _ _ _ iu).mpr uu,moved,s',(square _ _ _ is).mpr ss,played⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 档案与同一原迭代树的对应

源模型和根图属于档案所记的真实节点，支撑来自该节点的实际操作载荷。
树延伸保留全部对应；新行只使用同次延伸产生的节点、根边及扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_archive_links_d (o Q G E D : M.Domain) : Prop :=
  ∀ m r, ∀ s : Td_archive_row_d M.Domain, Rd_entry_d m r D → Rt_tuple_d s.values_d r →
    Rd_entry_d s.i s.c Q ∧ It_map_d G o s.i s.p ∧
      ∃ p κ F, Rd_entry_d s.i p E ∧ It_payload_d p κ s.L F

theorem Td_archive_links_d.empty_l {o Q G E D : M.Domain}
    (empty : ∀ x, ¬ M.mem x D) : Td_archive_links_d o Q G E D := by
  rintro m r s ⟨p,_,hp⟩ _
  exact (empty p hp).elim

/-- 旧节点的归属从原树模型列读取，故无需另给节点编号上界。 -/
theorem Td_archive_links_d.extend_l (hZF : M.Models ZF)
    {Ω c o α T Q G E ξ k β T' Q' G' E' D : M.Domain}
    (links : Td_archive_links_d o Q G E D)
    (tree : It_tree_d hZF Ω c α T Q G E)
    (extension : It_extension_d α ξ k T Q G E β T' Q' G' E') :
    Td_archive_links_d o Q' G' E' D := by
  intro m r s entry code
  obtain ⟨node,root,p,κ,F,move,payload⟩ := links m r s entry code
  have hi := (tree.diagram.model_domain s.i).mpr ⟨s.c,node⟩
  exact ⟨extension.2.2.1 s.i s.c node,(extension.2.2.2.1 o s.i s.p hi).mpr root,
    p,κ,F,extension.2.2.2.2.1 s.i p move,payload⟩

/-- 精确追加的行码决定同一源行，不重新选择模型、节点或根边。 -/
theorem Td_archive_links_d.push_l {o Q G E D D' m r p κ F : M.Domain}
    {s : Td_archive_row_d M.Domain} (links : Td_archive_links_d o Q G E D)
    (code : Rt_tuple_d s.values_d r) (node : Rd_entry_d s.i s.c Q)
    (root : It_map_d G o s.i s.p)
    (move : Rd_entry_d s.i p E) (payload : It_payload_d p κ s.L F)
    (append : ∀ n t, Rd_entry_d n t D' ↔ Rd_entry_d n t D ∨ n = m ∧ t = r) :
    Td_archive_links_d o Q G E D' := by
  intro n t a entry pack
  rcases (append n t).mp entry with entry | ⟨rfl,rfl⟩
  · exact links n t a entry pack
  · exact (Td_archive_row_d.eq_l (rt_tuple_inj_l pack code)).symm ▸ ⟨node,root,p,κ,F,move,payload⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原奇节点不落在当前偶节点的前驱中

偶数后继直接以旧偶节点为父，故新奇节点以及全部旧奇节点都不进入该前驱链。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_clear_d (D n T : M.Domain) : Prop := ∀ m r, ∀ s : Td_archive_row_d M.Domain,
  Rd_entry_d m r D → Rt_tuple_d s.values_d r → ¬ Rd_entry_d s.i n T

theorem Td_clear_d.empty_l {D n T : M.Domain} (empty : ∀ x, ¬ M.mem x D) : Td_clear_d D n T := by
  rintro m r s ⟨p,_,hp⟩ _
  exact (empty p hp).elim

theorem Td_clear_d.step_l (hZF : M.Models ZF)
    {Ω c o n m T Q G E θ T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ k D D' a r : M.Domain}
    {row : Td_archive_row_d M.Domain}
    (old : Td_clear_d D n T) (links : Td_archive_links_d o Q G E D)
    (tree : It_tree_d hZF Ω c m T Q G E) (succ : M.SuccessorOf m n)
    (mid : It_tree_d hZF Ω c θ T₁ Q₁ G₁ E₁)
    (first : It_extension_d m n k T Q G E θ T₁ Q₁ G₁ E₁)
    (second : It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂)
    (code : Rt_tuple_d row.values_d r) (index : row.i = m)
    (append : ∀ i s, Rd_entry_d i s D' ↔ Rd_entry_d i s D ∨ i = a ∧ s = r) : Td_clear_d D' θ T₂ := by
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have keep := (tree.extension_keep_l hZF first).1
  intro i t s entry pack edge
  have edge : s.i = θ ∨ Rd_entry_d s.i n T₁ := by
    rcases (second.2.1 s.i θ).mp edge with h | ⟨_,h⟩
    · exact (ir θ (mid.diagram.order.bound _ _ h).2).elim
    · exact h
  rcases (append i t).mp entry with entry | ⟨rfl,rfl⟩
  · have member := (tree.diagram.model_domain s.i).mpr ⟨s.c,(links i t s entry pack).1⟩
    rcases edge with eq | edge
    · exact ir θ (eq ▸ (first.1 s.i).mpr (Or.inl member))
    · exact old i t s entry pack ((keep s.i n succ.predecessor_mem).mp edge)
  · have eq := Td_archive_row_d.eq_l (rt_tuple_inj_l pack code)
    have index' : s.i = m := congrArg Td_archive_row_d.i eq |>.trans index
    rcases edge with eq | edge
    · exact ir θ (index'.symm.trans eq ▸ first.1.predecessor_mem)
    · exact ir m (index' ▸ (tree.diagram.order.bound _ _ ((keep s.i n succ.predecessor_mem).mp edge)).1)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 档案整列沿实际后继推进

统一界低于本次候选时，每个旧端点都落在同一低秩交换方块内。
共同层复合、原父边上的事件运输及数字图的行号保持逐行使用同一批像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} {Ar Sr : M.Domain} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_archive_d.step_l
    {Ω c₀ X₀ D cN N R cP P S μ ν U V Γ t j χ w z w' z' c e a h c' e' a' h' D₀ q q' : M.Domain}
    (old : Td_archive_d I Ω c₀ X₀ Ar Sr D N R χ c e a z h D₀ q)
    (step : Ic_common_d I N R P S μ ν U V Γ t)
    (hΩ : M.IsOmega Ω) (mn : Smdl_d I cN N R) (mp : Smdl_d I cP P S)
    (map : Smap_d I Ω cN cP N P j)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (ep : Rf_ext_d I P S)
    (numbers : Rr_layer_d I Ω N R w z) (numbers' : Rr_layer_d I Ω P S w' z')
    (κ K : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (rank : V_d (kp_pair_l hN) κ K) (below : Rd_entry_d κ.val μ R) (bound : Rd_entry_d χ κ.val R)
    (square : ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain,
      (smdl_structure_l I (R := R) mn.2.1).mem x K → ∀ E, Rd_entry_d x.val E t ↔ Rd_entry_d x.val E j)
    (roots : It_comp_d q j q')
    (points : ∀ i : Fin 4, Rd_entry_d ([c,e,a,h].get i) ([c',e',a',h'].get i) j) :
    Td_archive_d I Ω c₀ X₀ Ar Sr D P S ν c' e' a' z' h' D₀ q' := by
  have en : Rf_ext_d I N R := fun x hx y hy same =>
    congrArg Subtype.val (hN.1.eq_of_same_members
      (⟨x,hx⟩ : (smdl_structure_l I (R := R) mn.2.1).Domain) ⟨y,hy⟩
      (fun v => same v.val v.property))
  intro m r entry
  obtain ⟨s,code,source,l,W,Δ,g,common,upper,root,view⟩ := old m r entry
  have low : Rd_entry_d l κ.val R := upper.elim
    (fun h => (v_ordinal_l (kp_pair_l hN) rank).transitive
      ⟨χ,(mn.2.2.2 χ κ.val bound).1⟩ bound ⟨l,common.right_rank.1⟩ h)
    (fun eq => eq.symm ▸ bound)
  obtain ⟨l',W',g',next,cap,graph⟩ := step.native_archive_step_l hZF mn mp hN
    (ep.native_l I mp.2.1) κ K rank below square s.X s.R s.L l s.U W Δ g common low
  exact ⟨s,code,source,l',W',Δ,g',next,Or.inl cap,
    root.comp_l (common.graph_comp_l hZF next graph) roots,
    view.image_l hZF hΩ mn mp map en ep numbers numbers' points graph⟩

/-- 非重置的两次真实施加合成一次档案更新，当前事件沿原偶数父边搬运。 -/
theorem Td_archive_d.advance_l
    {Ω c₀ X₀ D N R P S Y T μ ν U V Γ t L l W Z Δ s cN cP cY j k κ χ
      w z w' z' c e a h c' e' a' h' D₀ q q' : M.Domain}
    (old : Td_archive_d I Ω c₀ X₀ Ar Sr D N R χ c e a z h D₀ q)
    (first : Ic_common_d I N R P S μ ν U V Γ t) (second : Ic_common_d I P S Y T L l W Z Δ s)
    (hΩ : M.IsOmega Ω) (mn : Smdl_d I cN N R) (mp : Smdl_d I cP P S) (my : Smdl_d I cY Y T)
    (map : Smap_d I Ω cN cY N Y j)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (hP : (smdl_structure_l I (R := S) mp.2.1).Models KP)
    (ey : Rf_ext_d I Y T)
    (numbers : Rr_layer_d I Ω N R w z) (numbers' : Rr_layer_d I Ω Y T w' z')
    (κ₀ K : (smdl_structure_l I (R := S) mp.2.1).Domain)
    (rank : V_d (kp_pair_l hP) κ₀ K) (point : Rd_entry_d κ κ₀.val t)
    (below : Rd_entry_d κ μ R) (above : Rd_entry_d κ₀.val L S) (bound : Rd_entry_d χ κ R)
    (inverse : ∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x t)
    (square : ∀ x : (smdl_structure_l I (R := S) mp.2.1).Domain, ∀ y E,
      (smdl_structure_l I (R := S) mp.2.1).mem x K → Rd_entry_d x.val y k →
        (Rd_entry_d x.val E s ↔ Rd_entry_d y E j))
    (roots : It_comp_d q j q')
    (points : ∀ i : Fin 4, Rd_entry_d ([c,e,a,h].get i) ([c',e',a',h'].get i) j) :
    Td_archive_d I Ω c₀ X₀ Ar Sr D Y T l c' e' a' z' h' D₀ q' := by
  let Nn := smdl_structure_l I (R := R) mn.2.1
  have en : Rf_ext_d I N R := fun x hx y hy same =>
    congrArg Subtype.val (hN.1.eq_of_same_members (⟨x,hx⟩ : Nn.Domain) ⟨y,hy⟩
      (fun v => same v.val v.property))
  have limit : Nn.IsLimitOrdinal ⟨μ,first.left_rank.1⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨μ,first.left_rank.1⟩)).mp first.limit)
  have ordinal := limit.1.mem (show Nn.mem ⟨κ,(mn.2.2.2 κ μ below).1⟩ ⟨μ,first.left_rank.1⟩ from below)
  intro m r entry
  obtain ⟨row,code,source,l₀,B,Dg,g,common,upper,root,view⟩ := old m r entry
  have low : Rd_entry_d l₀ κ R := upper.elim
    (fun h => ordinal.transitive ⟨χ,(mn.2.2.2 χ κ bound).1⟩ bound ⟨l₀,common.right_rank.1⟩ h)
    (fun eq => eq.symm ▸ bound)
  obtain ⟨l',B',g',next,cap,graph⟩ := first.native_archive_image_l hZF second mn mp my hN hP
    (ey.native_l I my.2.1) κ₀ K rank point below above inverse square
      row.X row.R row.L l₀ row.U B Dg g common low
  exact ⟨row,code,source,l',B',Dg,g',next,Or.inl cap,
    root.comp_l (common.graph_comp_l hZF next graph) roots,
    view.image_l hZF hΩ mn my map en ey numbers numbers' points graph⟩

end YesMetaZFC.SetTheory.LargeCardinal
