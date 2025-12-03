import Mathlib.Data.Int.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

inductive ThreeReg where
  | R1 | R2 | R3
  deriving DecidableEq, Repr

abbrev Val := Int

structure State where
  r1 : Val
  r2 : Val
  r3 : Val
  deriving Repr

def State.read (s : State) (r : ThreeReg) : Val :=
  match r with
  | .R1 => s.r1
  | .R2 => s.r2
  | .R3 => s.r3

def State.write (s : State) (r : ThreeReg) (v : Val) : State :=
  match r with
  | .R1 => { s with r1 := v }
  | .R2 => { s with r2 := v }
  | .R3 => { s with r3 := v }

@[ext] lemma State.ext (s t : State) :
  s.r1 = t.r1 → s.r2 = t.r2 → s.r3 = t.r3 → s = t := by
  cases s
  cases t
  intro h1 h2 h3
  cases h1
  cases h2
  cases h3
  rfl

@[ext] lemma State.ext_read (s t : State) :
  (∀ r : ThreeReg, s.read r = t.read r) → s = t := by
  intro h
  -- unfold both states and use the three registers
  cases s with
  | mk s1 s2 s3 =>
    cases t with
    | mk t1 t2 t3 =>
      have h1 := h ThreeReg.R1
      have h2 := h ThreeReg.R2
      have h3 := h ThreeReg.R3
      -- h1 : s1 = t1, etc.
      cases h1
      cases h2
      cases h3
      rfl

@[simp] lemma read_write_same (s : State) (r : ThreeReg) (v : Val) :
  (State.write s r v).read r = v := by
  cases r <;> cases s <;> simp [State.write, State.read]

@[simp] lemma read_write_ne (s : State) {r r' : ThreeReg} (v : Val) (h : r' ≠ r) :
  (State.write s r v).read r' = s.read r' := by
  cases r <;> cases r' <;> cases s <;> simp [State.write, State.read] at *

/-- Rename the registers of a state by σ. -/
def State.perm (σ : ThreeReg ≃ ThreeReg) (s : State) : State :=
  { r1 := s.read (σ.symm ThreeReg.R1)
    r2 := s.read (σ.symm ThreeReg.R2)
    r3 := s.read (σ.symm ThreeReg.R3) }

@[simp] lemma read_perm (σ : ThreeReg ≃ ThreeReg) (s : State) (r : ThreeReg) :
  (State.perm σ s).read r = s.read (σ.symm r) := by
  cases r <;> rfl

@[simp] lemma read_perm_apply
  (σ : ThreeReg ≃ ThreeReg) (s : State) (r : ThreeReg) :
  (State.perm σ s).read (σ r) = s.read r := by
  -- Start with read_perm specialized at σ r
  have := read_perm σ s (σ r)
  -- This states: (State.perm σ s).read (σ r) = s.read (σ.symm (σ r))
  -- Now rewrite σ.symm (σ r) to r
  simp [Equiv.symm_apply_apply]

lemma symm_eq_iff (σ : ThreeReg ≃ ThreeReg) (r r' : ThreeReg) :
  σ.symm r' = r ↔ r' = σ r := by
  constructor
  · intro h
    -- apply σ to both sides
    have := congrArg σ h
    -- σ (σ.symm r') = σ r → r' = σ r
    simpa [Equiv.apply_symm_apply] using this
  · intro h
    -- apply σ.symm to both sides
    have := congrArg σ.symm h
    -- σ.symm r' = σ.symm (σ r) = r
    simpa [Equiv.symm_apply_apply] using this

@[simp] lemma write_perm (σ : ThreeReg ≃ ThreeReg) (s : State) (r : ThreeReg) (v : Val) :
  State.perm σ (State.write s r v)
    = State.write (State.perm σ s) (σ r) v := by
  apply State.ext_read
  intro r'
  -- compare `read r'` on both sides
  -- Left:
  --   (State.perm σ (State.write s r v)).read r'
  -- = (State.write s r v).read (σ.symm r')        by read_perm
  -- Right:
  --   (State.write (State.perm σ s) (σ r) v).read r'
  --   is either v (if r' = σ r) or the old value.
  have h_eq : σ.symm r' = r ∨ σ.symm r' ≠ r := by
    by_cases h : σ.symm r' = r
    · exact Or.inl h
    · exact Or.inr h
  rcases h_eq with h | h
  · -- case σ.symm r' = r  ⇔ r' = σ r
    have hr' : r' = σ r := (symm_eq_iff σ r r').1 h
    -- LHS:
    simp [read_perm, h, read_write_same]   -- (σ.symm r' = r) ⇒ read gives v
    -- RHS:
    simp [hr', read_write_same]
  · -- case σ.symm r' ≠ r  ⇔ r' ≠ σ r
    have hr' : r' ≠ σ r := by
      -- contrapositive: r' = σ r ⇒ σ.symm r' = r
      intro hr'
      apply h
      exact (symm_eq_iff σ r r').2 hr'
    -- LHS:
    simp [read_perm, read_write_ne, h]
    -- RHS:
    simp [read_write_ne, hr']

/- Define the property of 3 distinct registers and its permutation -/
def distinct3 (i j k : ThreeReg) : Prop :=
  i ≠ j ∧ j ≠ k ∧ k ≠ i

lemma distinct3_map (σ : ThreeReg ≃ ThreeReg) {i j k} (h : distinct3 i j k) :
  distinct3 (σ i) (σ j) (σ k) := by
  rcases h with ⟨hij, hjk, hki⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hij'
    apply hij
    exact σ.injective hij'
  · intro hjk'
    apply hjk
    exact σ.injective hjk'
  · intro hki'
    apply hki
    exact σ.injective hki'

/- Now start defining instructions-/
inductive Instr where
  | load (x : Val) (dst : ThreeReg)
  | load_rev (x : Val) (dst : ThreeReg)
  | add_const (src : ThreeReg) (x : Val) (dst : ThreeReg) (h : src ≠ dst)
  | add_const_rev (src : ThreeReg) (x : Val) (dst : ThreeReg) (h : src ≠ dst)
  | add_reg (src1 src2 dst : ThreeReg) (h : distinct3 src1 src2 dst)
  | add_reg_rev (src1 src2 dst : ThreeReg) (h : distinct3 src1 src2 dst)
  | mul_const (src : ThreeReg) (x : Val) (dst : ThreeReg) (h : src ≠ dst)
  | mul_const_rev (src : ThreeReg) (x : Val) (dst : ThreeReg) (h : src ≠ dst)
  | mul_reg (src1 src2 dst : ThreeReg) (h : distinct3 src1 src2 dst)
  | mul_reg_rev (src1 src2 dst : ThreeReg) (h : distinct3 src1 src2 dst)
  deriving Repr

def Instr.perm (σ : ThreeReg ≃ ThreeReg) : Instr → Instr
  | .load x dst         => .load x (σ dst)
  | .load_rev x dst     => .load_rev x (σ dst)
  | .add_const src x dst h =>
      let h' : σ src ≠ σ dst := fun hσ => h (σ.injective hσ)
      .add_const (σ src) x (σ dst) h'
  | .add_const_rev src x dst h =>
      let h' : σ src ≠ σ dst := fun hσ => h (σ.injective hσ)
      .add_const_rev (σ src) x (σ dst) h'
  | .add_reg src1 src2 dst h =>
      .add_reg (σ src1) (σ src2) (σ dst) (distinct3_map σ h)
  | .add_reg_rev src1 src2 dst h =>
      .add_reg_rev (σ src1) (σ src2) (σ dst) (distinct3_map σ h)
  | .mul_const src x dst h =>
      let h' : σ src ≠ σ dst := fun hσ => h (σ.injective hσ)
      .mul_const (σ src) x (σ dst) h'
  | .mul_const_rev src x dst h =>
      let h' : σ src ≠ σ dst := fun hσ => h (σ.injective hσ)
      .mul_const_rev (σ src) x (σ dst) h'
  | .mul_reg src1 src2 dst h =>
      .mul_reg (σ src1) (σ src2) (σ dst) (distinct3_map σ h)
  | .mul_reg_rev src1 src2 dst h =>
      .mul_reg_rev (σ src1) (σ src2) (σ dst) (distinct3_map σ h)

-- Defining big step semantics for Instructions
def Instr.exec (i : Instr) (s : State) : State :=
  match i with
  | .load x dst =>
    let v := s.read dst + x
    s.write dst v
  | .load_rev x dst =>
    let v := s.read dst - x
    s.write dst v
  | .add_const src x dst _ =>
    let v := s.read dst + s.read src + x
    s.write dst v
  | .add_const_rev src x dst _ =>
    let v := s.read dst - (s.read src + x)
    s.write dst v
  | .add_reg src1 src2 dst _ =>
    let v := s.read dst + s.read src1 + s.read src2
    s.write dst v
  | .add_reg_rev src1 src2 dst _ =>
    let v := s.read dst - (s.read src1 + s.read src2)
    s.write dst v
  | .mul_const src x dst _ =>
    let v := s.read dst + x * s.read src
    s.write dst v
  | .mul_const_rev src x dst _ =>
    let v := s.read dst - x * s.read src
    s.write dst v
  | .mul_reg src1 src2 dst _ =>
    let v := s.read dst + s.read src1 * s.read src2
    s.write dst v
  | .mul_reg_rev src1 src2 dst _ =>
   let v := s.read dst - s.read src1 * s.read src2
   s.write dst v

lemma instr_exec_perm (σ : ThreeReg ≃ ThreeReg) (i : Instr) (s : State) :
  Instr.exec (Instr.perm σ i) (State.perm σ s)
    = State.perm σ (Instr.exec i s) := by
  cases i with
  | load x dst =>
      -- LHS: write (σ dst) ((State.perm σ s).read (σ dst) + x)
      -- RHS: perm (write dst (s.read dst + x))
      -- use read_perm_apply to identify the value, then write_perm
      simp [Instr.exec, Instr.perm, write_perm]
  | load_rev x dst =>
      simp [Instr.exec, Instr.perm, write_perm]
  | add_const src x dst h =>
      simp [Instr.exec, Instr.perm, write_perm, add_comm]
  | add_const_rev src x dst h =>
      simp [Instr.exec, Instr.perm, write_perm, sub_eq_add_neg, add_assoc, add_comm]
  | add_reg src1 src2 dst h =>
      simp [Instr.exec, Instr.perm, write_perm, add_comm, add_left_comm]
  | add_reg_rev src1 src2 dst h =>
      simp [Instr.exec, Instr.perm, write_perm, sub_eq_add_neg, add_assoc, add_comm]
  | mul_const src x dst h =>
      simp [Instr.exec, Instr.perm, write_perm, add_comm]
  | mul_const_rev src x dst h =>
      simp [Instr.exec, Instr.perm, write_perm, sub_eq_add_neg, add_comm]
  | mul_reg src1 src2 dst h =>
      simp [Instr.exec, Instr.perm, write_perm, add_comm]
  | mul_reg_rev src1 src2 dst h =>
      simp [Instr.exec, Instr.perm, write_perm, sub_eq_add_neg, add_comm]

/- Define the reverse for instructions-/
def Instr.rev : Instr → Instr
  | Instr.load x dst =>
      Instr.load_rev x dst

  | Instr.load_rev x dst =>
      Instr.load x dst


  | Instr.add_const src x dst h =>
      Instr.add_const_rev src x dst h

  | Instr.add_const_rev src x dst h =>
      Instr.add_const src x dst h


  | Instr.add_reg src1 src2 dst h =>
      Instr.add_reg_rev src1 src2 dst h

  | Instr.add_reg_rev src1 src2 dst h =>
      Instr.add_reg src1 src2 dst h


  | Instr.mul_const src x dst h =>
      Instr.mul_const_rev src x dst h

  | Instr.mul_const_rev src x dst h =>
      Instr.mul_const src x dst h


  | Instr.mul_reg src1 src2 dst h =>
      Instr.mul_reg_rev src1 src2 dst h

  | Instr.mul_reg_rev src1 src2 dst h =>
      Instr.mul_reg src1 src2 dst h

@[simp] lemma sub_add_add_cancel_val (a b c : Val) :
  a - (b + c) + b + c = a := by
  ring

lemma instr_rev (i : Instr) (s : State) :
  Instr.exec (Instr.rev i) (Instr.exec i s) = s := by
  apply State.ext_read
  intro r
  cases i with
  | load x dst =>
    by_cases hrd : r = dst
    · subst hrd
      simp [Instr.exec, Instr.rev, read_write_same, sub_eq_add_neg,
              add_comm, add_left_comm]
    ·
      simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, hrd, sub_eq_add_neg]
  | load_rev x dst =>
    by_cases hrd : r = dst
    · subst hrd
      simp [Instr.exec, Instr.rev, read_write_same, sub_eq_add_neg,
              add_comm]
    ·
      simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, hrd, sub_eq_add_neg]
  | add_const src x dst h =>
      -- v1 = s.read dst + s.read src + x
      -- v2 = v1 - (s.read src + x) = s.read dst
      by_cases hrd : r = dst
      · subst hrd
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h,
              sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h, hrd,
              sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  | add_const_rev src x dst h =>
      -- first subtract, then add back
      -- v1 = s.read dst - (s.read src + x)
      -- v2 = v1 + s.read src + x = s.read dst
      by_cases hrd : r = dst
      · subst hrd
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h,
              sub_eq_add_neg, add_comm, add_left_comm]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h, hrd,
              sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  | add_reg src1 src2 dst h =>
      -- v1 = dst + src1 + src2
      -- v2 = v1 - (src1 + src2) = dst
      by_cases hrd : r = dst
      · subst hrd
        have h_src1_ne_dst : src1 ≠ r := Ne.symm h.2.2
        have h_src2_ne_dst : src2 ≠ r := h.2.1
        simp [Instr.exec, Instr.rev,
              read_write_same,
              read_write_ne, h_src1_ne_dst, h_src2_ne_dst,
              sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc]
      ·
        simp [Instr.exec, Instr.rev, read_write_same, hrd]
  | add_reg_rev src1 src2 dst h =>
      -- v1 = dst - (src1 + src2)
      -- v2 = v1 + src1 + src2 = dst
      by_cases hrd : r = dst
      · subst hrd
        have h_src1_ne_dst : src1 ≠ r := Ne.symm h.2.2
        have h_src2_ne_dst : src2 ≠ r := h.2.1
        simp [Instr.exec, Instr.rev, read_write_same,
              h_src1_ne_dst, h_src2_ne_dst,
              sub_eq_add_neg, add_comm, add_left_comm]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, hrd,
              sub_eq_add_neg, add_comm, add_assoc]
  | mul_const src x dst h =>
      -- v1 = dst + x * src
      -- v2 = v1 - x * src = dst
      by_cases hrd : r = dst
      · subst hrd
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h,
              sub_eq_add_neg, add_comm, add_assoc]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h, hrd,
              sub_eq_add_neg, add_comm, add_left_comm]
  | mul_const_rev src x dst h =>
      -- v1 = dst - x * src
      -- v2 = v1 + x * src = dst
      by_cases hrd : r = dst
      · subst hrd
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h,
              sub_eq_add_neg, add_comm, add_left_comm]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, h, hrd,
              sub_eq_add_neg, add_comm]
  | mul_reg src1 src2 dst h =>
      -- v1 = dst + src1 * src2
      -- v2 = v1 - src1 * src2 = dst
      by_cases hrd : r = dst
      · subst hrd
        have h_src1_ne_dst : src1 ≠ r := Ne.symm h.2.2
        have h_src2_ne_dst : src2 ≠ r := h.2.1
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne,
              h_src1_ne_dst, h_src2_ne_dst,
              sub_eq_add_neg, add_comm, add_assoc]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, hrd,
              sub_eq_add_neg, add_comm, add_assoc]
  | mul_reg_rev src1 src2 dst h =>
      -- v1 = dst - src1 * src2
      -- v2 = v1 + src1 * src2 = dst
      by_cases hrd : r = dst
      · subst hrd
        have h_src1_ne_dst : src1 ≠ r := Ne.symm h.2.2
        have h_src2_ne_dst : src2 ≠ r := h.2.1
        simp [Instr.exec, Instr.rev, read_write_same, read_write_ne,
              sub_eq_add_neg, add_comm, add_left_comm,
              h_src1_ne_dst, h_src2_ne_dst]
      · simp [Instr.exec, Instr.rev, read_write_same, read_write_ne, hrd,
              sub_eq_add_neg, add_comm, add_assoc]

@[simp] lemma instr_rev_rev (i : Instr) : i.rev.rev = i := by
  cases i <;> rfl

lemma instr_rev2 (i : Instr) (s : State) :
  Instr.exec i (Instr.exec (Instr.rev i) s) = s := by
  -- use `instr_rev` on `i.rev`
  simpa [instr_rev_rev] using instr_rev (i := i.rev) (s := s)

/- Now we can define program, and permutations-/
abbrev Program := List Instr

def Program.perm (σ : ThreeReg ≃ ThreeReg) (p : Program) : Program :=
  p.map (Instr.perm σ)

def Program.exec : Program → State → State
  | [], s => s
  | i :: p, s => Program.exec p (Instr.exec i s)

def Program.rev : Program → Program
  | []      => []
  | i :: p  => Program.rev p ++ ([i.rev] : Program)

lemma exec_append (p q : Program) (s : State) :
  Program.exec (p ++ q) s = Program.exec q (Program.exec p s) := by
  induction p generalizing s with
  | nil =>
      simp [Program.exec]
  | cons i p ih =>
      simp [Program.exec, List.cons_append, ih]

lemma exec_perm (σ : ThreeReg ≃ ThreeReg) (p : Program) (s : State) :
  Program.exec (Program.perm σ p) (State.perm σ s)
    = State.perm σ (Program.exec p s) := by
  induction p generalizing s with
  | nil =>
      simp [Program.exec, Program.perm, State.perm]
  | cons i p ih =>
      have h' := ih (Instr.exec i s)
      simpa [Program.exec, Program.perm, instr_exec_perm] using h'

lemma exec_rev (p : Program) (s : State) :
  Program.exec (Program.rev p) (Program.exec p s) = s := by
  induction p generalizing s with
  | nil =>
      simp [Program.exec, Program.rev]
  | cons i p ih =>
      -- p = i :: p
      simp [Program.exec, Program.rev, exec_append, ih, instr_rev]

lemma exec_rev2 (p : Program) (s : State) :
  Program.exec p (Program.exec (Program.rev p) s) = s := by
  induction p generalizing s with
  | nil =>
      simp [Program.exec, Program.rev]
  | cons i p ih =>
      simp [Program.exec, Program.rev, exec_append, instr_rev2, ih]
