#include "View/PrimaryLineEdit.h"
#include "View/MainWindow.h"

#include <QKeyEvent>

PrimaryLineEdit::PrimaryLineEdit(QWidget*& parent):
    QLineEdit(parent), containsResult_(false) {
}

void PrimaryLineEdit::keyPressEvent(QKeyEvent* e) {
    QLineEdit::keyPressEvent(e);

    if (containsResult_) {
        // if it was a special key:
        if (e->text().isEmpty()) {
            if (Qt::Key_Delete == e->key() || Qt::Key_Backspace == e->key()) {
                setText("");
                setBold(false);
                containsResult_ = false;
            }
        } else { // if there was a text input:
            addToText(e->text());
        }
    }
}

void PrimaryLineEdit::setBold(bool enabled) {
    QFont boldFont = this->font();
    boldFont.setBold(enabled);
    this->setFont(boldFont);
}

void PrimaryLineEdit::mousePressEvent(QMouseEvent* e) {
    if (containsResult_) {
        // then we change the text to Ans
        // so that the user can calculate with the real result
        // instead of the approximation
        this->setText("Ans ");
        this->setBold(false);
        containsResult_ = false;
    }

    QLineEdit::mousePressEvent(e);
}

void PrimaryLineEdit::addToText(const QString& str) {
    this->setFocus();

    // for some reason, on an enter, this gets called with "\r"
    // so we have to do something about it
    if (0 < str.length() && "\r" != str) {
        // a space or enter will not toggle the flag
        if (containsResult_) {
            this->setBold(false);
            containsResult_ = false;
            if (str.endsWith('(')) {
                this->setText(str + "Ans");
            } else if (str.at(0).isLetterOrNumber()) {
                this->setText(str);
            } else {
                this->setText("Ans" + str);
            }
        } else {
            this->setText(this->text() + str);
        }
    }
}

void PrimaryLineEdit::setResult(const QString& str) {
    this->setText(str);
    this->setBold(true);
    containsResult_ = true;
}

void PrimaryLineEdit::setBack() {
    this->setText("");
    this->setBold(false);
    containsResult_ = false;
}

bool PrimaryLineEdit::containsResult() const {
    return containsResult_;
}
