import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAgreementRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch

/-! # 原关系复制在有限幂子集上的交换条件

只要求所属图与父模型图在实际有限幂的子集上交换。实际隶属实例中的
原有 Ea_maps 条件直接产生此证书，不增加整个共同层上的一致性前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Er_maps_d (ω N T κ z k k' π σ : M.Domain) : Prop :=
  ∀ n m d a a' A A', M.mem n ω → Rd_entry_d n m z → Er_space_d I N T κ m d →
    M.mem a N → (∀ x, M.mem x N → Rd_entry_d x a T → Rd_entry_d x d T) →
    Rd_entry_d a A k → Rd_entry_d a a' σ → Rd_entry_d A A' π → Rd_entry_d a' A' k'

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem Ea_maps_d.raw_l {ω κ N T N' X Y c Γ Γ' z k k' π σ : M.Domain}
    (h : Ea_maps_d ω κ X π σ) (fs : Fs_read_d ω N) (mx : Smem_d Kp c N T) (hκ : M.mem κ N)
    (fπ : M.IsSetFunctionFromTo Kp π X Y) (fσ : M.IsSetFunctionFromTo Kp σ N N')
    (zs : ∀ n m, Rd_entry_d n m z ↔ M.mem n ω ∧ n = m)
    (ks : ∀ a A, Rd_entry_d a A k ↔ M.mem a Γ ∧ a = A)
    (gs' : ∀ a, M.mem a Γ' ↔ M.mem a N' ∧ M.mem a Y)
    (ks' : ∀ a A, Rd_entry_d a A k' ↔ M.mem a Γ' ∧ a = A) :
    Er_maps_d Kp ω N T κ z k k' π σ := by
  intro n m d a a' A A' hn hnm space ha sub hak haa hAA
  obtain ⟨_, rfl⟩ := (zs n m).mp hnm
  obtain ⟨_, rfl⟩ := (ks a A).mp hak
  have bound : M.MemberSubset a d := fun x hx => ((mx.2 x d).mp
    (sub x (fs.transitive a ha x hx) ((mx.2 x a).mpr ⟨fs.transitive a ha x hx, ha, hx⟩))).2.2
  have moved := h n d a A' hn ((er_space_mem_l Kp hZF.1 fs mx hκ hn).mp space).2
    (fπ.input_mem_of_pairMember hAA) bound hAA
  have eq := fσ.1.2 a a' A' haa moved
  exact (ks' a' A').mpr ⟨(gs' a').mpr
    ⟨fσ.output_mem_of_pairMember haa, eq.symm ▸ fπ.output_mem_of_pairMember hAA⟩, eq⟩

/-- 有限幂中的点以单点子集识别；原子集交换条件因此也强制逐点交换。 -/
theorem Er_maps_d.point_l {ω c N T c' N' T' σ h X R h' Y S π Γ Γ' k k' κ κ' z z'
    n m d x x' A A' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d Kp c N T) (my : Smdl_d Kp c' N' T')
    (map : Smap_d Kp ω c c' N N' σ) (ext : Rf_ext_d Kp N T)
    (parent : Smdl_d Kp h X R) (parent' : Smdl_d Kp h' Y S)
    (copy : Smap_d Kp ω h h' X Y π) (px : Rf_ext_d Kp X R)
    (agree : Er_agree_d Kp ω N T κ z Γ X R k)
    (agree' : Er_agree_d Kp ω N' T' κ' z' Γ' Y S k')
    (maps : Er_maps_d Kp ω N T κ z k k' π σ)
    (hn : M.mem n ω) (hnm : Rd_entry_d n m z) (space : Er_space_d Kp N T κ m d)
    (hx : M.mem x N)
    (single : ∃ a : (smdl_structure_l Kp (R := T) mx.2.1).Domain,
      Pair_d (smdl_structure_l Kp (R := T) mx.2.1) a ⟨x, hx⟩ ⟨x, hx⟩)
    (hxd : Rd_entry_d x d T)
    (hxA : Rd_entry_d x A k) (hxx : Rd_entry_d x x' σ) (hAA : Rd_entry_d A A' π) :
    Rd_entry_d x' A' k' := by
  have ext' : Rf_ext_d Kp N' T' := map.extensional_l hZF hω mx my ext
  have py : Rf_ext_d Kp Y S := copy.extensional_l hZF hω parent parent' px
  have ex := ext.native_l Kp mx.2.1
  have ey := ext'.native_l Kp my.2.1
  have ep := px.native_l Kp parent.2.1
  have ep' := py.native_l Kp parent'.2.1
  let x₀ : (smdl_structure_l Kp (R := T) mx.2.1).Domain := ⟨x, hx⟩
  let x₁ : (smdl_structure_l Kp (R := T') my.2.1).Domain := ⟨x', map.1.1.output_mem_of_pairMember hxx⟩
  obtain ⟨a, singleton⟩ := single
  have sub y (hy : M.mem y N) (hya : Rd_entry_d y a.val T) : Rd_entry_d y d T := by
    have eq : y = x := congrArg Subtype.val (((singleton ⟨y, hy⟩).mp hya).elim id id)
    exact eq.symm ▸ hxd
  obtain ⟨_, _, front, _⟩ := agree.powers n m d hn hnm space
  obtain ⟨B, hB, haB⟩ := agree.injection.1.2.2 a.val (front a.val a.property sub)
  obtain ⟨a', ha', haa⟩ := map.1.1.2.2 a.val a.property
  obtain ⟨B', hB', hBB⟩ := copy.1.1.2.2 B hB
  have haB' := maps n m d a.val a' B B' hn hnm space a.property sub haB haa hBB
  let a₁ : (smdl_structure_l Kp (R := T') my.2.1).Domain := ⟨a', ha'⟩
  let ρ : Env (smdl_structure_l Kp (R := T) mx.2.1) 2 := ⟨Fin.cases a (fun _ => x₀), fun _ => a⟩
  let η : Env (smdl_structure_l Kp (R := T') my.2.1) 2 := ⟨Fin.cases a₁ (fun _ => x₁), fun _ => a₁⟩
  have singleton' : Pair_d (smdl_structure_l Kp (R := T') my.2.1) a₁ x₁ x₁ :=
    (pair0_sat_l ey ..).mp ((smap_source_l Kp hZF hω mx my map (pair0_m .newest (.bound 1) (.bound 1))
      (by simp -implicitDefEqProofs) ρ η (Fin.cases haa (fun _ => hxx))).mp ((pair0_sat_l ex ..).mpr singleton))
  let A₀ : (smdl_structure_l Kp (R := R) parent.2.1).Domain := ⟨A, copy.1.1.input_mem_of_pairMember hAA⟩
  let B₀ : (smdl_structure_l Kp (R := R) parent.2.1).Domain := ⟨B, hB⟩
  let A₁ : (smdl_structure_l Kp (R := S) parent'.2.1).Domain := ⟨A', copy.1.1.output_mem_of_pairMember hAA⟩
  let B₁ : (smdl_structure_l Kp (R := S) parent'.2.1).Domain := ⟨B', hB'⟩
  have singleB : Pair_d (smdl_structure_l Kp (R := R) parent.2.1) B₀ A₀ A₀ := by
    intro y
    constructor
    · intro hy
      obtain ⟨s, hsa, hsy⟩ := (agree.predecessors a.val B haB y.val).mp hy
      have hs := agree.domain s (agree.injection.1.input_mem_of_pairMember hsy)
      have eq : s = x := congrArg Subtype.val (((singleton ⟨s, hs⟩).mp hsa).elim id id)
      exact Or.inl (Subtype.ext (agree.injection.1.1.2 x y.val A (eq ▸ hsy) hxA))
    · intro hy
      have eq : y.val = A := congrArg Subtype.val (hy.elim id id)
      change Rd_entry_d y.val B R
      exact eq.symm ▸ (agree.predecessors a.val B haB A).mpr
        ⟨x, (singleton x₀).mpr (Or.inl rfl), hxA⟩
  let ρ₀ : Env (smdl_structure_l Kp (R := R) parent.2.1) 2 := ⟨Fin.cases B₀ (fun _ => A₀), fun _ => B₀⟩
  let η₀ : Env (smdl_structure_l Kp (R := S) parent'.2.1) 2 := ⟨Fin.cases B₁ (fun _ => A₁), fun _ => B₁⟩
  have singleB' : Pair_d (smdl_structure_l Kp (R := S) parent'.2.1) B₁ A₁ A₁ :=
    (pair0_sat_l ep' ..).mp ((smap_source_l Kp hZF hω parent parent' copy (pair0_m .newest (.bound 1) (.bound 1))
      (by simp -implicitDefEqProofs) ρ₀ η₀ (Fin.cases hBB (fun _ => hAA))).mp ((pair0_sat_l ep ..).mpr singleB))
  obtain ⟨s, hsa, hsA⟩ := (agree'.predecessors a' B' haB' A').mp ((singleB' A₁).mpr (Or.inl rfl))
  have hs := agree'.domain s (agree'.injection.1.input_mem_of_pairMember hsA)
  have eq : s = x' := congrArg Subtype.val (((singleton' ⟨s, hs⟩).mp hsa).elim id id)
  exact eq ▸ hsA

end YesMetaZFC.SetTheory.LargeCardinal
